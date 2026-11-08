module

public import CatalanMeasure.GenD.Signed.RouteI.CompactHf
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.MomentInputs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section
set_option Elab.async false

/-!
# Route I `NearDataCert`: the data-side facts of the near `hf` for the actual source

Theorem side only. For `capSource` (`CapSourceData`):

* `nearDataClosed_capSource : NearDataClosed capSource`, that is
  - `k = 1..32`: the closed-form moment sum of `reflMoment_closed` is within `1/10000` of `muL k`;
  - `k = 1..32`: `|radCoef capSource k - alL k| <= 1/10000`;
  - `sum_{k=33}^{384} |radCoef capSource k| <= 1/200`;
* `nearHf_capSource : NearHf capSource (Trunc.finite 384)` by `CompactHf.nearHf_closed`.

**Moments.** `vY` at a cell end `a / 10^12` is `(Y - sqrt (Y^2 - 4)) / 2`. The integer square root `s` of
`a^2 - 4 * 10^24` is found by Newton steps and only *checked* (`s^2 <= n < (s+1)^2`), which encloses `vY` in an
interval of length `1 / (2 * 10^12)` (`vY_enc`, `vhat_spec`). With `V = floor (vhat * 2^48)` the power sums
`PS_j = sum_c rho_c (v_lo^j - v_hi^j)`, `j <= 33`, are the base-`Y` digits of one natural number: each cell
contributes the closed-form geometric series `sum_j (V Y)^j` (`geom_pack`, `packTot_digit`), so all powers of all
cells cost a handful of big-number operations. `m_k = PS_(k-1)/(k-1) - PS_(k+1)/(k+1)` (`mom_ge2`); for `k = 1` the
logarithm of the cell ratio is a five-term polynomial in `t = V_lo / V_hi - 1 <= 3/100` whose powers are packed the
same way (`Plog`, `log_cell`, `mom_one`). Errors are carried by `cell_data`, `pow_diff_cell`, `ps_err`.

**Radial coefficients.** `radCoef k = - (tgt / M) c_k Z_k` with `c_k = (1 + S k + C k^2) / k` and
`Z_k = sum_e p_e (q rad_e)^k cos (k pi j_e / 93)` (`radCoef_form`). `q`, `rad_i` come from `Real.exp_bound`
(the radii as fourth powers of `exp (-sigma / 4)`), `S`, `C` from their rational forms in `q^2` with the Lipschitz
bounds `fS_lip`, `fC_lip`. The cosines are `Re (w^m)`, `w = exp (i pi / 93)`, from the exact Gaussian integer powers
of a 48-bit rational approximation of `w` (`cpow_err`, `cos_err`, `u_spec`) stored as digits of one natural number
`TC`; `cos (k pi j / 93) = cos (m pi / 93)`, `m = k j mod 186`. The weights `p_e` of the 680 auxiliary entries sit in
one natural number indexed by `(radius, phase)` (`regroup`, `Wm_eq`), the 16 radii of a phase form one digit
vector, so a row `sum_j u_(kj) W_j` is a single dot product against it (`Sk_digit`, `Tk_cast`, `Zhat_eq`).
`rad_err` gives `|radCoef k - RhatQ k| <= ErrQ k`.

**Tail.** For `33 <= k <= 68` the same enclosure bounds `|radCoef k|` by `|RhatQ k| + ErrQ k`; for `k > 68` the
cosine is bounded by `1` and the radii are grouped (`WR`, `WR_sum`, `maj_err`).

kcost: the two `decide +kernel` declarations below (`momKernel_true` 3.5 s, `radialKernel_true` 7.5 s measured on
6 Nov, standalone `lean`) are all the kernel work of this module (about 11 K in total); there is no generated data.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.NearDataCert

open CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (muL alL momK radCoef NearDataClosed)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_le_one vY_pos)

/-- Base-`B` digit extraction from a finite digit sum. -/
theorem digit_sum (B : ℕ) (hB : 0 < B) :
    ∀ (N : ℕ) (a : ℕ → ℕ), (∀ m < N, a m < B) → ∀ m < N,
      (∑ i ∈ Finset.range N, a i * B ^ i) / B ^ m % B = a m := by
  intro N
  induction N with
  | zero => intro a _ m hm; omega
  | succ N ih =>
    intro a ha m hm
    rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range N, a (i + 1) * B ^ (i + 1) =
        B * ∑ i ∈ Finset.range N, a (i + 1) * B ^ i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h1]
    simp only [pow_zero, mul_one]
    have ha0 : a 0 < B := ha 0 (by omega)
    rcases m with _ | m
    · simp only [pow_zero, Nat.div_one]
      rw [add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt ha0
    · have e : (B * ∑ i ∈ Finset.range N, a (i + 1) * B ^ i + a 0) / B ^ (m + 1) =
          (∑ i ∈ Finset.range N, a (i + 1) * B ^ i) / B ^ m := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_add_div hB,
          Nat.div_eq_of_lt ha0, add_zero]
      rw [e]
      exact ih (fun i => a (i + 1)) (fun i hi => ha (i + 1) (by omega)) m (by omega)

/-- Regrouping a weighted list sum by an index function. -/
theorem regroup {α R : Type*} [CommSemiring R] (L : List α) (idx : α → ℕ) (N : ℕ)
    (hN : ∀ t ∈ L, idx t < N) (f : α → R) (G : ℕ → R) :
    (L.map fun t => f t * G (idx t)).sum =
      ∑ m ∈ Finset.range N, (L.map fun t => if idx t = m then f t else 0).sum * G m := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have h1 : ∀ s ∈ L, idx s < N := fun s hs => hN s (List.mem_cons_of_mem _ hs)
    have h0 : idx t < N := hN t (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    rw [ih h1]
    have : f t * G (idx t) = ∑ m ∈ Finset.range N, (if idx t = m then f t else 0) * G m := by
      simp [ite_mul, Finset.sum_ite_eq, h0]
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _; ring

theorem geom_pack (V Y n : ℕ) (h : 2 ≤ V * Y) :
    ((V * Y) ^ n - 1) / (V * Y - 1) = ∑ j ∈ Finset.range n, V ^ j * Y ^ j := by
  rw [← Nat.geomSum_eq h n]
  apply Finset.sum_congr rfl; intro j _; rw [mul_pow]

def packTot {α : Type*} (r v : α → ℕ) (Y n : ℕ) (L : List α) : ℕ :=
  (L.map fun c => r c * (((v c * Y) ^ n - 1) / (v c * Y - 1))).sum

theorem packTot_eq {α : Type*} (r v : α → ℕ) (Y n : ℕ) (L : List α)
    (h : ∀ c ∈ L, 2 ≤ v c * Y) :
    packTot r v Y n L = ∑ j ∈ Finset.range n, (L.map fun c => r c * v c ^ j).sum * Y ^ j := by
  induction L with
  | nil => simp [packTot]
  | cons c L ih =>
    have h1 : ∀ s ∈ L, 2 ≤ v s * Y := fun s hs => h s (List.mem_cons_of_mem _ hs)
    have ih' := ih h1
    unfold packTot at ih' ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ih', geom_pack _ _ _ (h c (List.mem_cons_self ..)), Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring

theorem packTot_digit {α : Type*} (r v : α → ℕ) (Y n : ℕ) (L : List α) (hY : 0 < Y)
    (h : ∀ c ∈ L, 2 ≤ v c * Y) (hb : ∀ j < n, (L.map fun c => r c * v c ^ j).sum < Y)
    (j : ℕ) (hj : j < n) :
    packTot r v Y n L / Y ^ j % Y = (L.map fun c => r c * v c ^ j).sum := by
  rw [packTot_eq r v Y n L h]
  exact digit_sum Y hY n (fun j => (L.map fun c => r c * v c ^ j).sum) hb j hj

theorem nat_div_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) * d ≤ n ∧ (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * d := by
  have h := Nat.div_add_mod n d
  have h2 := Nat.mod_lt n hd
  have hR : ((d * (n / d) + n % d : ℕ) : ℝ) = n := by exact_mod_cast h
  push_cast at hR
  have : ((n % d : ℕ) : ℝ) < d := by exact_mod_cast h2
  have h0 : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> nlinarith

/-- cell-coordinate scale `10^12` -/
def KC : ℕ := 10 ^ 12
theorem KC_real : (KC : ℝ) = 10 ^ 12 := by unfold KC; push_cast; norm_num


/-! ### Square-root enclosure of `vY` at the cell endpoints -/

theorem vY_enc (K a s : ℕ) (hK : 0 < K) (ha : 2 * K ≤ a) (h1 : s * s ≤ a * a - 4 * (K * K))
    (h2 : a * a - 4 * (K * K) < (s + 1) * (s + 1)) :
    |vY ((a : ℝ) / K) - (2 * a - 2 * s - 1) / (4 * K)| ≤ 1 / (4 * K) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have haR : (2 : ℝ) * K ≤ a := by exact_mod_cast ha
  have hsq : 4 * (K * K) ≤ a * a := by nlinarith
  have hn : ((a * a - 4 * (K * K) : ℕ) : ℝ) = (a : ℝ) ^ 2 - 4 * K ^ 2 := by
    rw [Nat.cast_sub hsq]; push_cast; ring
  have h1R : (s : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 - 4 * K ^ 2 := by
    rw [← hn]; exact_mod_cast (by nlinarith : s ^ 2 ≤ a * a - 4 * (K * K))
  have h2R : (a : ℝ) ^ 2 - 4 * K ^ 2 < ((s : ℝ) + 1) ^ 2 := by
    rw [← hn]; exact_mod_cast (by nlinarith : a * a - 4 * (K * K) < (s + 1) ^ 2)
  set n : ℝ := (a : ℝ) ^ 2 - 4 * K ^ 2 with hnd
  have hn0 : 0 ≤ n := by nlinarith
  have hY : ((a : ℝ) / K) ^ 2 - 4 = n / (K : ℝ) ^ 2 := by
    rw [hnd]; field_simp
  have hsqrt : Real.sqrt (((a : ℝ) / K) ^ 2 - 4) = Real.sqrt n / K := by
    rw [hY, Real.sqrt_div hn0, Real.sqrt_sq hKR.le]
  have hlo : (s : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le h1R
  have hhi : Real.sqrt n ≤ (s : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; exact h2R.le
  unfold vY
  rw [hsqrt]
  have e : (((a : ℝ) / K - Real.sqrt n / K) / 2 - (2 * a - 2 * s - 1) / (4 * K)) =
      (2 * s + 1 - 2 * Real.sqrt n) / (4 * K) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * K)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]; constructor <;> linarith

/-- abstract clamp-and-floor step -/
theorem clamp_floor (K P X v : ℝ) (c : ℕ) (hK : 0 < K) (hP : 0 < P)
    (hc1 : (c : ℝ) * (4 * K) ≤ X * P) (hc2 : X * P < ((c : ℝ) + 1) * (4 * K))
    (hv : |v - X / (4 * K)| ≤ 1 / (4 * K)) (hv1 : v ≤ 1) :
    |v - min P c / P| ≤ 1 / (4 * K) + 1 / P := by
  have hw : X / (4 * K) = X * P / (4 * K) / P := by field_simp
  set w : ℝ := X / (4 * K) with hwdef
  have hw1 : (c : ℝ) / P ≤ w := by
    rw [hwdef, div_le_div_iff₀ hP (by positivity)]; nlinarith
  have hw2 : w < (c : ℝ) / P + 1 / P := by
    rw [hwdef, ← add_div, div_lt_div_iff₀ (by positivity) hP]; nlinarith
  have hpos : 0 < 1 / P := by positivity
  rw [abs_le] at hv ⊢
  rcases le_total (c : ℝ) P with hle | hle
  · rw [min_eq_right hle]
    constructor <;> linarith [hv.1, hv.2]
  · rw [min_eq_left hle, div_self hP.ne']
    have hw3 : 1 ≤ w := by
      calc (1 : ℝ) ≤ c / P := by rw [le_div_iff₀ hP]; linarith
        _ ≤ w := hw1
    have : 0 < 1 / (4 * K) := by positivity
    constructor <;> linarith [hv.1, hv.2]

def isqrtF (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => if (x + n / x) / 2 < x then isqrtF n f ((x + n / x) / 2) else x
def isqrt (n : ℕ) : ℕ := isqrtF n 64 (2 ^ (n.log2 / 2 + 1))

def PM : ℕ := 48
theorem PM_real : ((2 : ℝ) ^ PM) = 281474976710656 := by unfold PM; norm_num

def vhat (a : ℕ) : ℕ :=
  min (2 ^ PM) (((2 * a - 2 * isqrt (a * a - 4 * (KC * KC)) - 1) * 2 ^ PM) / (4 * KC))

def vOk (a : ℕ) : Bool :=
  decide (2 * KC ≤ a) &&
  decide (isqrt (a * a - 4 * (KC * KC)) * isqrt (a * a - 4 * (KC * KC)) ≤ a * a - 4 * (KC * KC)) &&
  decide (a * a - 4 * (KC * KC) < (isqrt (a * a - 4 * (KC * KC)) + 1) * (isqrt (a * a - 4 * (KC * KC)) + 1)) &&
  decide (isqrt (a * a - 4 * (KC * KC)) + 1 ≤ a) &&
  decide (9 * 2 ^ PM ≤ 100 * vhat a)

theorem vhat_spec (a : ℕ) (h : vOk a = true) :
    |vY ((a : ℝ) / KC) - (vhat a : ℝ) / 2 ^ PM| ≤ 3 / 10 ^ 13 ∧
      (vhat a : ℝ) / 2 ^ PM ≤ 1 ∧ (9 : ℝ) / 100 ≤ (vhat a : ℝ) / 2 ^ PM ∧
      (2 : ℝ) ≤ (a : ℝ) / KC := by
  unfold vOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, h1⟩, h2⟩, h3⟩, h4⟩ := h
  set s := isqrt (a * a - 4 * (KC * KC)) with hs
  have hKpos : 0 < KC := by unfold KC; norm_num
  have henc := vY_enc KC a s hKpos ha h1 h2
  have hKp : (0 : ℝ) < KC := by exact_mod_cast hKpos
  have hP : (0 : ℝ) < 2 ^ PM := by positivity
  have h3R : ((s : ℝ) + 1) ≤ a := by exact_mod_cast h3
  have haR : (2 : ℝ) * KC ≤ a := by exact_mod_cast ha
  have hdiv := nat_div_bounds ((2 * a - 2 * s - 1) * 2 ^ PM) (4 * KC) (by omega)
  set c : ℕ := ((2 * a - 2 * s - 1) * 2 ^ PM) / (4 * KC) with hc
  have hsub : ((2 * a - 2 * s - 1 : ℕ) : ℝ) = 2 * a - 2 * s - 1 := by
    have h5 : 2 * s + 1 ≤ 2 * a := by omega
    have h6 : 2 * a - 2 * s - 1 = 2 * a - (2 * s + 1) := by omega
    rw [h6, Nat.cast_sub h5]; push_cast; ring
  have hnumR : (((2 * a - 2 * s - 1) * 2 ^ PM : ℕ) : ℝ) = (2 * a - 2 * s - 1) * 2 ^ PM := by
    rw [Nat.cast_mul, hsub]; push_cast; ring
  rw [hnumR] at hdiv
  obtain ⟨hc1, hc2⟩ := hdiv
  push_cast at hc1 hc2
  have hv1 : vY ((a : ℝ) / KC) ≤ 1 := vY_le_one (by rw [le_div_iff₀ hKp]; linarith)
  have hcl := clamp_floor (KC : ℝ) (2 ^ PM) (2 * a - 2 * s - 1) (vY ((a : ℝ) / KC)) c hKp hP
    hc1 hc2 henc hv1
  have hmin : (vhat a : ℝ) = min (2 ^ PM : ℝ) c := by
    show ((min (2 ^ PM) c : ℕ) : ℝ) = _
    rw [Nat.cast_min]; push_cast; rfl
  have hq : 1 / (4 * (KC : ℝ)) + 1 / (2 ^ PM : ℝ) ≤ 3 / 10 ^ 13 := by
    rw [KC_real, PM_real]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmin]; exact hcl.trans hq
  · rw [hmin, div_le_one hP]; exact min_le_left _ _
  · have : (9 * 2 ^ PM : ℝ) ≤ 100 * (vhat a : ℝ) := by exact_mod_cast h4
    rw [le_div_iff₀ hP]; linarith
  · rw [le_div_iff₀ hKp]; linarith


/-! ### The positive gas cells as natural-number triples -/

def R0 : ℕ := 48
def R2 : ℕ := 48
def NJ : ℕ := 34
def YB : ℕ := 2 ^ 1700 + 1
def TT : ℕ := (sumP row0).toNat
def gasN : List (ℕ × ℕ × ℕ) := gasPosT.map fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)
def rtl (c : ℕ × ℕ × ℕ) : ℕ := (c.2.2 * KC * 2 ^ R0) / (TT * (c.2.1 - c.1))
def mrow (c : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (rtl c, vhat c.1, vhat c.2.1)
def mrows : List (ℕ × ℕ × ℕ) := gasN.map mrow
def AT : ℕ := packTot (fun m => m.1) (fun m => m.2.1) YB NJ mrows
def BT : ℕ := packTot (fun m => m.1) (fun m => m.2.2) YB NJ mrows
def Aj (j : ℕ) : ℕ := AT / YB ^ j % YB
def Bj (j : ℕ) : ℕ := BT / YB ^ j % YB

def cellOk (c : ℕ × ℕ × ℕ) : Bool :=
  vOk c.1 && vOk c.2.1 && decide (c.1 < c.2.1) && decide (vhat c.2.1 ≤ vhat c.1) &&
  decide (100 * (vhat c.1 - vhat c.2.1) ≤ 3 * vhat c.2.1) &&
  decide (0 < TT * (c.2.1 - c.1)) &&
  decide (vhat c.2.1 ≤ (vhat c.1 - vhat c.2.1) * 2 ^ R2)

noncomputable def rhoR (c : ℕ × ℕ × ℕ) : ℝ :=
  (c.2.2 : ℝ) / (TT : ℝ) / (((c.2.1 : ℝ) - c.1) / KC)

noncomputable def cellTerm (k : ℕ) (c : ℕ × ℕ × ℕ) : ℝ :=
  rhoR c * (momK k (vY (c.1 / KC)) - momK k (vY (c.2.1 / KC)))

theorem TT_real : (TT : ℝ) = (sumP row0 : ℝ) := by
  unfold TT
  have h : (0 : ℤ) ≤ sumP row0 := row0_tot.le
  have := Int.toNat_of_nonneg h
  exact_mod_cast this

theorem gasN_mem {c : ℕ × ℕ × ℕ} (h : c ∈ gasN) :
    ∃ t ∈ gasPosT, c = (t.1.toNat, t.2.1.toNat, t.2.2.toNat) := by
  unfold gasN at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ⟨t, ht, rfl⟩

theorem gas_valid {t : Tr} (ht : t ∈ gasPosT) : 0 ≤ t.1 ∧ t.1 < t.2.1 ∧ 0 ≤ t.2.2 := by
  obtain ⟨hm, hp⟩ := List.mem_filter.1 (show t ∈ row0.filter isPos from ht)
  have hnn : 0 ≤ t.1 := by simpa [isPos] using hp
  exact ⟨hnn, (row0_ok t hm).1, (row0_ok t hm).2⟩

theorem gas_conv (k : ℕ) :
    ((capSource.gas Sign.pos).map fun c => c.w / (c.hi - c.lo) *
        (momK k (vY c.lo) - momK k (vY c.hi))).sum = (gasN.map (cellTerm k)).sum := by
  show ((gasPosT.map (mkCell 1 (sumP row0))).map _).sum = _
  rw [List.map_map]
  unfold gasN
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro t ht
  obtain ⟨h0, h1, h2⟩ := gas_valid ht
  obtain ⟨hlo, hhi, hw⟩ := mkCell_eq (m := 1) (T := sumP row0) ⟨h1, h2⟩ row0_tot.le zero_le_one
  simp only [Function.comp]
  rw [hlo, hhi, hw]
  unfold cellTerm rhoR
  have e1 : ((t.1.toNat : ℕ) : ℝ) = (t.1 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
  have e2 : ((t.2.1.toNat : ℕ) : ℝ) = (t.2.1 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ t.2.1)
  have e3 : ((t.2.2.toNat : ℕ) : ℝ) = (t.2.2 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h2
  simp only [e1, e2, e3, TT_real, KC_real]
  congr 1
  · congr 1
    · ring
    · ring

/-! ### Cell-level facts -/

theorem pow_diff_cell (ρ r δ : ℝ) (x y x' y' ε : ℝ) (j : ℕ)
    (hr0 : 0 ≤ r) (hrρ : r ≤ ρ) (hρr : ρ ≤ r + δ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1) (hy0' : 0 ≤ y') (hy1' : y' ≤ 1)
    (hxe : |x - x'| ≤ ε) (hye : |y - y'| ≤ ε) :
    |ρ * (x ^ j - y ^ j) - r * (x' ^ j - y' ^ j)| ≤ ρ * (2 * j * ε) + δ := by
  have hρ0 : 0 ≤ ρ := hr0.trans hrρ
  have h1 := CatalanMeasure.GenD.Signed.RouteI.MomentInputs.abs_pow_sub_pow_le_unit hx0 hx1 hx0' hx1' j
  have h2 := CatalanMeasure.GenD.Signed.RouteI.MomentInputs.abs_pow_sub_pow_le_unit hy0 hy1 hy0' hy1' j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have h1' : |x ^ j - x' ^ j| ≤ j * ε := h1.trans (mul_le_mul_of_nonneg_left hxe hj)
  have h2' : |y ^ j - y' ^ j| ≤ j * ε := h2.trans (mul_le_mul_of_nonneg_left hye hj)
  have hd : |(x ^ j - y ^ j) - (x' ^ j - y' ^ j)| ≤ 2 * j * ε := by
    have e : (x ^ j - y ^ j) - (x' ^ j - y' ^ j) = (x ^ j - x' ^ j) - (y ^ j - y' ^ j) := by ring
    rw [e]
    have := abs_sub (x ^ j - x' ^ j) (y ^ j - y' ^ j)
    linarith
  have hb : |x' ^ j - y' ^ j| ≤ 1 := by
    have a1 : 0 ≤ x' ^ j := pow_nonneg hx0' _
    have a2 : x' ^ j ≤ 1 := pow_le_one₀ hx0' hx1'
    have a3 : 0 ≤ y' ^ j := pow_nonneg hy0' _
    have a4 : y' ^ j ≤ 1 := pow_le_one₀ hy0' hy1'
    rw [abs_le]; constructor <;> linarith
  have e : ρ * (x ^ j - y ^ j) - r * (x' ^ j - y' ^ j) =
      ρ * ((x ^ j - y ^ j) - (x' ^ j - y' ^ j)) + (ρ - r) * (x' ^ j - y' ^ j) := by ring
  rw [e]
  calc _ ≤ |ρ * ((x ^ j - y ^ j) - (x' ^ j - y' ^ j))| + |(ρ - r) * (x' ^ j - y' ^ j)| := abs_add_le _ _
    _ = ρ * |(x ^ j - y ^ j) - (x' ^ j - y' ^ j)| + (ρ - r) * |x' ^ j - y' ^ j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρ0, abs_of_nonneg (by linarith : 0 ≤ ρ - r)]
    _ ≤ ρ * (2 * j * ε) + δ * 1 := by
        apply add_le_add (mul_le_mul_of_nonneg_left hd hρ0)
        exact mul_le_mul (by linarith) hb (abs_nonneg _) (by linarith [hr0, hρr, hrρ])
    _ = _ := by ring

theorem rho_bounds (c : ℕ × ℕ × ℕ) (h : 0 < TT * (c.2.1 - c.1)) (hlt : c.1 < c.2.1) :
    ((rtl c : ℕ) : ℝ) / 2 ^ R0 ≤ rhoR c ∧ rhoR c < ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0 := by
  have hd := nat_div_bounds (c.2.2 * KC * 2 ^ R0) (TT * (c.2.1 - c.1)) h
  have hT : (0 : ℝ) < TT := by
    have : 0 < TT := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h)
    exact_mod_cast this
  have hK : (0 : ℝ) < KC := by unfold KC; norm_num
  have hba : (0 : ℝ) < (c.2.1 : ℝ) - c.1 := by
    have : (c.1 : ℝ) < c.2.1 := by exact_mod_cast hlt
    linarith
  have hsub : ((c.2.1 - c.1 : ℕ) : ℝ) = (c.2.1 : ℝ) - c.1 := by
    rw [Nat.cast_sub hlt.le]
  have hP : (0 : ℝ) < 2 ^ R0 := by positivity
  push_cast [hsub] at hd
  obtain ⟨h1, h2⟩ := hd
  have hrho : rhoR c = (c.2.2 : ℝ) * KC / (TT * ((c.2.1 : ℝ) - c.1)) := by
    unfold rhoR; field_simp
  have hden : (0 : ℝ) < TT * ((c.2.1 : ℝ) - c.1) := mul_pos hT hba
  unfold rtl
  constructor
  · rw [hrho, div_le_div_iff₀ hP hden]
    linarith
  · rw [hrho, ← add_div, div_lt_div_iff₀ hden hP]
    linarith


/-! ### Exact power sums of the positive gas cells -/

noncomputable def vlo (c : ℕ × ℕ × ℕ) : ℝ := vY ((c.1 : ℝ) / KC)
noncomputable def vhi (c : ℕ × ℕ × ℕ) : ℝ := vY ((c.2.1 : ℝ) / KC)
noncomputable def xlo (c : ℕ × ℕ × ℕ) : ℝ := (vhat c.1 : ℝ) / 2 ^ PM
noncomputable def xhi (c : ℕ × ℕ × ℕ) : ℝ := (vhat c.2.1 : ℝ) / 2 ^ PM

theorem cell_data {c : ℕ × ℕ × ℕ} (h : cellOk c = true) :
    ((rtl c : ℕ) : ℝ) / 2 ^ R0 ≤ rhoR c ∧ rhoR c < ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0 ∧
    |vlo c - xlo c| ≤ 3 / 10 ^ 13 ∧ |vhi c - xhi c| ≤ 3 / 10 ^ 13 ∧
    0 ≤ vlo c ∧ vlo c ≤ 1 ∧ 0 ≤ vhi c ∧ vhi c ≤ 1 ∧
    0 ≤ xlo c ∧ xlo c ≤ 1 ∧ 0 ≤ xhi c ∧ xhi c ≤ 1 ∧
    (9 : ℝ) / 100 ≤ xlo c ∧ (9 : ℝ) / 100 ≤ xhi c ∧ xhi c ≤ xlo c ∧ xlo c - xhi c ≤ 3 / 100 * xhi c := by
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  obtain ⟨rb1, rb2⟩ := rho_bounds c h6 h3
  obtain ⟨e1, u1, l1, g1⟩ := vhat_spec c.1 h1
  obtain ⟨e2, u2, l2, g2⟩ := vhat_spec c.2.1 h2
  have hP : (0 : ℝ) < 2 ^ PM := by positivity
  have p1 : 0 ≤ vlo c := by unfold vlo; exact (vY_pos g1).le
  have q1 : vlo c ≤ 1 := by unfold vlo; exact vY_le_one g1
  have p2 : 0 ≤ vhi c := by unfold vhi; exact (vY_pos g2).le
  have q2 : vhi c ≤ 1 := by unfold vhi; exact vY_le_one g2
  have p3 : 0 ≤ xlo c := div_nonneg (Nat.cast_nonneg _) hP.le
  have p4 : 0 ≤ xhi c := div_nonneg (Nat.cast_nonneg _) hP.le
  have e1' : |vlo c - xlo c| ≤ 3 / 10 ^ 13 := e1
  have e2' : |vhi c - xhi c| ≤ 3 / 10 ^ 13 := e2
  have u1' : xlo c ≤ 1 := u1
  have u2' : xhi c ≤ 1 := u2
  have l1' : (9 : ℝ) / 100 ≤ xlo c := l1
  have l2' : (9 : ℝ) / 100 ≤ xhi c := l2
  refine ⟨rb1, rb2, e1', e2', p1, q1, p2, q2, p3, u1', p4, u2', l1', l2', ?_, ?_⟩
  · unfold xlo xhi
    exact div_le_div_of_nonneg_right (by exact_mod_cast h4) hP.le
  · unfold xlo xhi
    have h5R : (100 : ℝ) * ((vhat c.1 : ℝ) - vhat c.2.1) ≤ 3 * vhat c.2.1 := by
      have : (vhat c.2.1 : ℕ) ≤ vhat c.1 := h4
      have := (Nat.cast_sub this : (((vhat c.1 - vhat c.2.1 : ℕ)) : ℝ) = (vhat c.1 : ℝ) - vhat c.2.1)
      rw [← this]; exact_mod_cast h5
    rw [← sub_div, ← mul_div_assoc, div_le_div_iff_of_pos_right hP]
    linarith


/-! ### Power sums: packed digits against the exact sums -/

noncomputable def psTrue (j : ℕ) : ℝ := (gasN.map fun c => rhoR c * (vlo c ^ j - vhi c ^ j)).sum

def psQ (j : ℕ) : ℚ := ((Aj j : ℤ) - (Bj j : ℤ)) / (2 : ℚ) ^ (R0 + PM * j)

def lenQ : ℚ := gasN.length
def sumR : ℚ := ((gasN.map rtl).sum : ℚ) / 2 ^ R0
/-- bound of the power-sum error, `j` = exponent -/
def errPs (j : ℕ) : ℚ :=
  2 * j * (3 / 10 ^ 13) * (sumR + lenQ / 2 ^ R0) + lenQ / 2 ^ R0

theorem sum_cast_nat {α : Type*} (L : List α) (f : α → ℕ) :
    (((L.map f).sum : ℕ) : ℝ) = (L.map fun c => (f c : ℝ)).sum := by
  rw [Nat.cast_list_sum, List.map_map]; rfl

theorem digit_gen {α : Type*} (L : List α) (r w : α → ℕ) (Y n M : ℕ) (hY2 : 2 ≤ Y)
    (hbound : (L.map r).sum * M ^ (n - 1) < Y) (hM : 1 ≤ M) (j : ℕ) (hj : j < n)
    (hv : ∀ m ∈ L, 1 ≤ w m ∧ w m ≤ M) :
    packTot r w Y n L / Y ^ j % Y = (L.map fun m => r m * w m ^ j).sum := by
  have hY : 0 < Y := by omega
  exact packTot_digit r w Y n L hY
    (fun m hm => by have := (hv m hm).1; nlinarith) (fun j hj => by
      calc (L.map fun c => r c * w c ^ j).sum
          ≤ (L.map fun c => r c * M ^ j).sum := by
            apply List.sum_le_sum; intro m hm
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hv m hm).2 _)
        _ = (L.map r).sum * M ^ j := by
            rw [List.sum_map_mul_right]
        _ ≤ (L.map r).sum * M ^ (n - 1) := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) (by omega)
        _ < Y := hbound) j hj

theorem yb2 : 2 ≤ YB := by
  unfold YB; have : 1 ≤ 2 ^ 1700 := Nat.one_le_two_pow; omega

theorem mrows_sum (f : ℕ × ℕ × ℕ → ℕ) :
    (mrows.map f).sum = (gasN.map fun c => f (mrow c)).sum := by
  unfold mrows; rw [List.map_map]; rfl

theorem Aj_eq (hb : (mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB) (j : ℕ) (hj : j < NJ)
    (hv : ∀ m ∈ mrows, 1 ≤ m.2.1 ∧ m.2.1 ≤ 2 ^ PM) :
    Aj j = (gasN.map fun c => rtl c * vhat c.1 ^ j).sum := by
  have := digit_gen mrows (fun m => m.1) (fun m => m.2.1) YB NJ (2 ^ PM) yb2 hb (Nat.one_le_two_pow) j hj hv
  unfold Aj AT
  rw [this, mrows_sum (fun m => m.1 * m.2.1 ^ j)]
  rfl

theorem Bj_eq (hb : (mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB) (j : ℕ) (hj : j < NJ)
    (hv : ∀ m ∈ mrows, 1 ≤ m.2.2 ∧ m.2.2 ≤ 2 ^ PM) :
    Bj j = (gasN.map fun c => rtl c * vhat c.2.1 ^ j).sum := by
  have := digit_gen mrows (fun m => m.1) (fun m => m.2.2) YB NJ (2 ^ PM) yb2 hb (Nat.one_le_two_pow) j hj hv
  unfold Bj BT
  rw [this, mrows_sum (fun m => m.1 * m.2.2 ^ j)]
  rfl


theorem vhat_bounds {a : ℕ} (h : vOk a = true) : 1 ≤ vhat a ∧ vhat a ≤ 2 ^ PM := by
  constructor
  · unfold vOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have h4 := h.2
    have : 0 < 2 ^ PM := by positivity
    omega
  · exact min_le_left _ _

theorem mrows_mem {m : ℕ × ℕ × ℕ} (h : m ∈ mrows) : ∃ c ∈ gasN, m = mrow c := by
  unfold mrows at h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
  exact ⟨c, hc, rfl⟩

theorem cellOk_vOk {c : ℕ × ℕ × ℕ} (h : cellOk c = true) : vOk c.1 = true ∧ vOk c.2.1 = true := by
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2⟩

theorem list_sum_sub {α : Type*} (L : List α) (f g : α → ℝ) :
    (L.map fun c => f c - g c).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_const {α : Type*} (L : List α) (d : ℝ) :
    (L.map fun _ => d).sum = L.length * d := by
  simp [List.map_const', List.sum_replicate]

theorem ps_err (hall : ∀ c ∈ gasN, cellOk c = true)
    (hb : (mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB) (j : ℕ) (hj : j < NJ) :
    |psTrue j - (psQ j : ℝ)| ≤ (errPs j : ℝ) := by
  have hvA : ∀ m ∈ mrows, 1 ≤ m.2.1 ∧ m.2.1 ≤ 2 ^ PM := by
    intro m hm
    obtain ⟨c, hc, rfl⟩ := mrows_mem hm
    exact vhat_bounds (cellOk_vOk (hall c hc)).1
  have hvB : ∀ m ∈ mrows, 1 ≤ m.2.2 ∧ m.2.2 ≤ 2 ^ PM := by
    intro m hm
    obtain ⟨c, hc, rfl⟩ := mrows_mem hm
    exact vhat_bounds (cellOk_vOk (hall c hc)).2
  have hA := Aj_eq hb j hj hvA
  have hB := Bj_eq hb j hj hvB
  -- the approximating sum
  set g' : ℕ × ℕ × ℕ → ℝ := fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 * (xlo c ^ j - xhi c ^ j) with hg'
  have hP : (0 : ℝ) < 2 ^ PM := by positivity
  have hR : (0 : ℝ) < 2 ^ R0 := by positivity
  have hsum : (gasN.map g').sum = (((Aj j : ℤ) - (Bj j : ℤ) : ℤ) : ℝ) / 2 ^ (R0 + PM * j) := by
    have e1 : ((Aj j : ℕ) : ℝ) = (gasN.map fun c => ((rtl c : ℕ) : ℝ) * ((vhat c.1 : ℕ) : ℝ) ^ j).sum := by
      rw [hA, sum_cast_nat]; push_cast; rfl
    have e2 : ((Bj j : ℕ) : ℝ) = (gasN.map fun c => ((rtl c : ℕ) : ℝ) * ((vhat c.2.1 : ℕ) : ℝ) ^ j).sum := by
      rw [hB, sum_cast_nat]; push_cast; rfl
    have e3 : ∀ c : ℕ × ℕ × ℕ, g' c = (((rtl c : ℕ) : ℝ) * ((vhat c.1 : ℕ) : ℝ) ^ j -
        ((rtl c : ℕ) : ℝ) * ((vhat c.2.1 : ℕ) : ℝ) ^ j) * (1 / 2 ^ (R0 + PM * j)) := by
      intro c
      simp only [hg', xlo, xhi]
      rw [div_pow, div_pow, pow_add, pow_mul]
      field_simp
    have e4 : (gasN.map g') = gasN.map (fun c => (((rtl c : ℕ) : ℝ) * ((vhat c.1 : ℕ) : ℝ) ^ j -
        ((rtl c : ℕ) : ℝ) * ((vhat c.2.1 : ℕ) : ℝ) ^ j) * (1 / 2 ^ (R0 + PM * j))) :=
      List.map_congr_left (fun c _ => e3 c)
    rw [e4, List.sum_map_mul_right, list_sum_sub, ← e1, ← e2]
    push_cast
    ring
  have hlen : ∀ c ∈ gasN, |rhoR c * (vlo c ^ j - vhi c ^ j) - g' c| ≤
      rhoR c * (2 * j * (3 / 10 ^ 13)) + 1 / 2 ^ R0 := by
    intro c hc
    obtain ⟨r1, r2, e1, e2, p1, q1, p2, q2, p3, u1, p4, u2, l1, l2, o1, o2⟩ := cell_data (hall c hc)
    have hr0 : 0 ≤ ((rtl c : ℕ) : ℝ) / 2 ^ R0 := div_nonneg (Nat.cast_nonneg _) hR.le
    exact pow_diff_cell (rhoR c) (((rtl c : ℕ) : ℝ) / 2 ^ R0) (1 / 2 ^ R0) (vlo c) (vhi c) (xlo c) (xhi c)
      (3 / 10 ^ 13) j hr0 r1 (by linarith) p1 q1 p2 q2 p3 u1 p4 u2 e1 e2
  have hmain := MomentSource.list_abs_sum_le gasN (fun c => rhoR c * (vlo c ^ j - vhi c ^ j)) g'
    (fun c => rhoR c * (2 * j * (3 / 10 ^ 13)) + 1 / 2 ^ R0) hlen
  -- sum of the error terms
  have hrho : (gasN.map rhoR).sum ≤ (sumR : ℝ) + (lenQ : ℝ) / 2 ^ R0 := by
    have h1 : (gasN.map rhoR).sum ≤ (gasN.map fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0).sum := by
      apply List.sum_le_sum; intro c hc
      exact (cell_data (hall c hc)).2.1.le
    have h2 : (gasN.map fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0).sum =
        (((gasN.map rtl).sum : ℕ) : ℝ) / 2 ^ R0 + gasN.length * (1 / 2 ^ R0) := by
      simp only [div_eq_mul_inv]
      rw [List.sum_map_add, List.sum_map_mul_right, sum_cast_nat]
      have := list_sum_const gasN (1 * ((2 : ℝ) ^ R0)⁻¹)
      simp only [one_mul] at this ⊢
      rw [this]
    rw [h2] at h1
    have hs : (sumR : ℝ) = (((gasN.map rtl).sum : ℕ) : ℝ) / 2 ^ R0 := by
      simp only [sumR, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
    have hl : (lenQ : ℝ) = gasN.length := by simp [lenQ]
    rw [hs, hl]
    have e : (gasN.length : ℝ) / 2 ^ R0 = gasN.length * (1 / 2 ^ R0) := by ring
    rw [e]
    exact h1
  have hj0 : (0 : ℝ) ≤ 2 * j * (3 / 10 ^ 13) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)
  have hS : (sumR : ℝ) = (((gasN.map rtl).sum : ℕ) : ℝ) / 2 ^ R0 := by
    simp only [sumR, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  have hl : (lenQ : ℝ) = gasN.length := by simp [lenQ]
  have hE : (gasN.map fun c => rhoR c * (2 * j * (3 / 10 ^ 13)) + 1 / 2 ^ R0).sum ≤ (errPs j : ℝ) := by
    rw [List.sum_map_add, List.sum_map_mul_right, list_sum_const]
    have e : (errPs j : ℝ) = 2 * j * (3 / 10 ^ 13) * ((sumR : ℝ) + (lenQ : ℝ) / 2 ^ R0) +
        (lenQ : ℝ) / 2 ^ R0 := by
      unfold errPs; push_cast; ring
    rw [e]
    have h3 := mul_le_mul_of_nonneg_right hrho hj0
    have e2 : (lenQ : ℝ) / 2 ^ R0 = gasN.length * (1 / 2 ^ R0) := by rw [hl]; ring
    rw [e2] at h3 ⊢
    linarith
  have hpsQ : (psQ j : ℝ) = (((Aj j : ℤ) - (Bj j : ℤ) : ℤ) : ℝ) / 2 ^ (R0 + PM * j) := by
    unfold psQ; push_cast; rfl
  unfold psTrue
  rw [hpsQ, ← hsum]
  exact hmain.trans hE

/-! ### Moments `k ≥ 2` -/

def momQ (k : ℕ) : ℚ := psQ (k - 1) / ((k : ℚ) - 1) - psQ (k + 1) / ((k : ℚ) + 1)
def momErr (k : ℕ) : ℚ := errPs (k - 1) / ((k : ℚ) - 1) + errPs (k + 1) / ((k : ℚ) + 1)

theorem mom_ge2 (hall : ∀ c ∈ gasN, cellOk c = true)
    (hb : (mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB) (k : ℕ) (hk : 2 ≤ k)
    (hkn : k + 1 < NJ) :
    |(gasN.map (cellTerm k)).sum - (momQ k : ℝ)| ≤ (momErr k : ℝ) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hpos1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hpos2 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hj1 : k - 1 < NJ := by omega
  have e1 : ∀ c : ℕ × ℕ × ℕ, cellTerm k c =
      rhoR c * (vlo c ^ (k - 1) - vhi c ^ (k - 1)) * (1 / ((k : ℝ) - 1)) -
      rhoR c * (vlo c ^ (k + 1) - vhi c ^ (k + 1)) * (1 / ((k : ℝ) + 1)) := by
    intro c
    unfold cellTerm momK vlo vhi
    simp only [show k ≠ 1 by omega, ite_false]
    field_simp
    ring
  have e2 : (gasN.map (cellTerm k)).sum = psTrue (k - 1) * (1 / ((k : ℝ) - 1)) -
      psTrue (k + 1) * (1 / ((k : ℝ) + 1)) := by
    rw [List.map_congr_left (fun c _ => e1 c), list_sum_sub, List.sum_map_mul_right,
      List.sum_map_mul_right]
    rfl
  have h1 := ps_err hall hb (k - 1) hj1
  have h2 := ps_err hall hb (k + 1) hkn
  have e3 : (momQ k : ℝ) = (psQ (k - 1) : ℝ) * (1 / ((k : ℝ) - 1)) -
      (psQ (k + 1) : ℝ) * (1 / ((k : ℝ) + 1)) := by
    unfold momQ; push_cast; ring
  have e4 : (momErr k : ℝ) = (errPs (k - 1) : ℝ) * (1 / ((k : ℝ) - 1)) +
      (errPs (k + 1) : ℝ) * (1 / ((k : ℝ) + 1)) := by
    unfold momErr; push_cast; ring
  rw [e2, e3, e4]
  have a1 : 0 < 1 / ((k : ℝ) - 1) := by positivity
  have a2 : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have f : psTrue (k - 1) * (1 / ((k : ℝ) - 1)) - psTrue (k + 1) * (1 / ((k : ℝ) + 1)) -
      ((psQ (k - 1) : ℝ) * (1 / ((k : ℝ) - 1)) - (psQ (k + 1) : ℝ) * (1 / ((k : ℝ) + 1))) =
      (psTrue (k - 1) - psQ (k - 1)) * (1 / ((k : ℝ) - 1)) -
      (psTrue (k + 1) - psQ (k + 1)) * (1 / ((k : ℝ) + 1)) := by ring
  rw [f]
  calc _ ≤ |(psTrue (k - 1) - psQ (k - 1)) * (1 / ((k : ℝ) - 1))| +
        |(psTrue (k + 1) - psQ (k + 1)) * (1 / ((k : ℝ) + 1))| := abs_sub _ _
    _ = |psTrue (k - 1) - psQ (k - 1)| * (1 / ((k : ℝ) - 1)) +
        |psTrue (k + 1) - psQ (k + 1)| * (1 / ((k : ℝ) + 1)) := by
        rw [abs_mul, abs_mul, abs_of_pos a1, abs_of_pos a2]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right h1 a1.le) (mul_le_mul_of_nonneg_right h2 a2.le)


/-! ### The moment `k = 1` (logarithm) -/

/-- five-term logarithm polynomial: `log (1 + t) ≈ Σ_{i<5} (-1)^i t^(i+1) / (i+1)` -/
noncomputable def Plog (t : ℝ) : ℝ := ∑ i ∈ Finset.range 5, (-1) ^ i * t ^ (i + 1) / ((i : ℝ) + 1)

theorem log_series_err {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 100) :
    |Real.log (1 + t) - Plog t| ≤ (3 / 100) ^ 6 / (1 - 3 / 100) := by
  have hx : |(-t)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  have e : (∑ i ∈ Finset.range 5, (-t) ^ (i + 1) / ((i : ℝ) + 1)) = -Plog t := by
    unfold Plog
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [neg_pow, pow_succ]; ring
  rw [e, show (1 : ℝ) - -t = 1 + t by ring, abs_neg, abs_of_nonneg h0] at h
  have h2 : |Real.log (1 + t) - Plog t| = |-Plog t + Real.log (1 + t)| := by
    rw [show -Plog t + Real.log (1 + t) = Real.log (1 + t) - Plog t by ring]
  rw [h2]
  refine h.trans ?_
  have h3 : t ^ 6 ≤ (3 / 100) ^ 6 := pow_le_pow_left₀ h0 h1 6
  calc t ^ (5 + 1) / (1 - t) ≤ (3 / 100) ^ 6 / (1 - t) := by
        apply div_le_div_of_nonneg_right h3; linarith
    _ ≤ (3 / 100) ^ 6 / (1 - 3 / 100) := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

theorem Plog_lip {t t' : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h0' : 0 ≤ t') (h1' : t' ≤ 1) :
    |Plog t - Plog t'| ≤ 5 * |t - t'| := by
  unfold Plog
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.range 5, |(-1 : ℝ) ^ i * t ^ (i + 1) / ((i : ℝ) + 1) -
      (-1) ^ i * t' ^ (i + 1) / ((i : ℝ) + 1)| ≤ |t - t'| := by
    intro i _
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have e : (-1 : ℝ) ^ i * t ^ (i + 1) / ((i : ℝ) + 1) - (-1) ^ i * t' ^ (i + 1) / ((i : ℝ) + 1) =
        (-1) ^ i * (t ^ (i + 1) - t' ^ (i + 1)) / ((i : ℝ) + 1) := by ring
    rw [e, abs_div, abs_mul, abs_of_pos hi, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      div_le_iff₀ hi]
    have := CatalanMeasure.GenD.Signed.RouteI.MomentInputs.abs_pow_sub_pow_le_unit h0 h1 h0' h1' (i + 1)
    push_cast at this
    linarith
  calc _ ≤ ∑ _i ∈ Finset.range 5, |t - t'| := Finset.sum_le_sum this
    _ = 5 * |t - t'| := by simp

theorem Plog_bd {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : |Plog t| ≤ 5 := by
  unfold Plog
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.range 5, |(-1 : ℝ) ^ i * t ^ (i + 1) / ((i : ℝ) + 1)| ≤ 1 := by
    intro i _
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by have : (0 : ℝ) ≤ i := Nat.cast_nonneg _; linarith
    rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (i : ℝ) + 1), abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_pow, abs_of_nonneg h0, div_le_one (by linarith)]
    calc t ^ (i + 1) ≤ 1 := pow_le_one₀ h0 h1
      _ ≤ _ := hi
  calc _ ≤ ∑ _i ∈ Finset.range 5, (1 : ℝ) := Finset.sum_le_sum this
    _ = 5 := by simp

def tau (c : ℕ × ℕ × ℕ) : ℕ := ((vhat c.1 - vhat c.2.1) * 2 ^ R2) / vhat c.2.1

noncomputable def tR (c : ℕ × ℕ × ℕ) : ℝ := (tau c : ℝ) / 2 ^ R2

/-- log-cell error -/
def eL : ℚ := 2 * (3 / 10 ^ 13) / (89 / 1000) + (3 / 100) ^ 6 / (1 - 3 / 100) + 5 / 2 ^ R2

theorem log_cell {c : ℕ × ℕ × ℕ} (h : cellOk c = true) :
    |(Real.log (vlo c) - Real.log (vhi c)) - Plog (tR c)| ≤ (eL : ℝ) ∧ 0 ≤ tR c ∧ tR c ≤ 3 / 100 := by
  obtain ⟨r1, r2, e1, e2, p1, q1, p2, q2, p3, u1, p4, u2, l1, l2, o1, o2⟩ := cell_data h
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hV2 : (0 : ℝ) < (vhat c.2.1 : ℝ) := by
    have := (vhat_bounds h2).1
    exact_mod_cast this
  have hP : (0 : ℝ) < 2 ^ PM := by positivity
  have hQ : (0 : ℝ) < 2 ^ R2 := by positivity
  -- floor facts for tau
  have hd := nat_div_bounds ((vhat c.1 - vhat c.2.1) * 2 ^ R2) (vhat c.2.1) (by exact_mod_cast hV2)
  have hsub : (((vhat c.1 - vhat c.2.1 : ℕ)) : ℝ) = (vhat c.1 : ℝ) - vhat c.2.1 := Nat.cast_sub h4
  push_cast [hsub] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have htau : (tau c : ℝ) * vhat c.2.1 ≤ ((vhat c.1 : ℝ) - vhat c.2.1) * 2 ^ R2 := hd1
  have htau2 : ((vhat c.1 : ℝ) - vhat c.2.1) * 2 ^ R2 < ((tau c : ℝ) + 1) * vhat c.2.1 := hd2
  -- te = xlo/xhi - 1
  set te : ℝ := xlo c / xhi c - 1 with hte
  have hxhi : 0 < xhi c := lt_of_lt_of_le (by norm_num) l2
  have hxlo : 0 < xlo c := lt_of_lt_of_le (by norm_num) l1
  have hte_eq : te = ((vhat c.1 : ℝ) - vhat c.2.1) / vhat c.2.1 := by
    rw [hte]; unfold xlo xhi; field_simp
  have hte0 : 0 ≤ te := by
    rw [hte_eq]; apply div_nonneg _ hV2.le
    have : (vhat c.2.1 : ℝ) ≤ vhat c.1 := by exact_mod_cast h4
    linarith
  have hte1 : te ≤ 3 / 100 := by
    rw [hte, sub_le_iff_le_add, div_le_iff₀ hxhi]
    linarith
  have ht1 : tR c ≤ te := by
    unfold tR; rw [hte_eq, div_le_div_iff₀ hQ hV2]; linarith
  have ht2 : te < tR c + 1 / 2 ^ R2 := by
    unfold tR; rw [hte_eq, ← add_div, div_lt_div_iff₀ hV2 hQ]; linarith
  have ht0 : 0 ≤ tR c := div_nonneg (Nat.cast_nonneg _) hQ.le
  have ht3 : tR c ≤ 3 / 100 := ht1.trans hte1
  refine ⟨?_, ht0, ht3⟩
  -- three pieces
  have hmin1 : (89 : ℝ) / 1000 ≤ min (vlo c) (xlo c) := by
    apply le_min
    · have := (abs_le.mp e1).1; linarith
    · linarith
  have hmin2 : (89 : ℝ) / 1000 ≤ min (vhi c) (xhi c) := by
    apply le_min
    · have := (abs_le.mp e2).1; linarith
    · linarith
  have d1 := MomentSource.abs_log_sub_le (lt_of_lt_of_le (by norm_num) (hmin1.trans (min_le_left _ _))) hxlo
  have d2 := MomentSource.abs_log_sub_le (lt_of_lt_of_le (by norm_num) (hmin2.trans (min_le_left _ _))) hxhi
  have d1' : |Real.log (vlo c) - Real.log (xlo c)| ≤ (3 / 10 ^ 13) / (89 / 1000) := by
    refine d1.trans ?_
    calc _ ≤ (3 / 10 ^ 13) / min (vlo c) (xlo c) :=
          div_le_div_of_nonneg_right e1 (by linarith [hmin1])
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmin1
  have d2' : |Real.log (vhi c) - Real.log (xhi c)| ≤ (3 / 10 ^ 13) / (89 / 1000) := by
    refine d2.trans ?_
    calc _ ≤ (3 / 10 ^ 13) / min (vhi c) (xhi c) :=
          div_le_div_of_nonneg_right e2 (by linarith [hmin2])
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmin2
  have e3 : Real.log (xlo c) - Real.log (xhi c) = Real.log (1 + te) := by
    rw [← Real.log_div hxlo.ne' hxhi.ne', hte]; ring_nf
  have s1 := log_series_err hte0 hte1
  have s2 := Plog_lip hte0 (by linarith) ht0 (by linarith)
  have s3 : |te - tR c| ≤ 1 / 2 ^ R2 := by
    rw [abs_le]; constructor <;> linarith
  have eLr : (eL : ℝ) = 2 * (3 / 10 ^ 13) / (89 / 1000) + (3 / 100) ^ 6 / (1 - 3 / 100) + 5 / 2 ^ R2 := by
    unfold eL; push_cast; ring
  have key : (Real.log (vlo c) - Real.log (vhi c)) - Plog (tR c) =
      ((Real.log (vlo c) - Real.log (xlo c)) - (Real.log (vhi c) - Real.log (xhi c))) +
      (Real.log (1 + te) - Plog te) + (Plog te - Plog (tR c)) := by
    rw [← e3]; ring
  rw [key, eLr]
  have t1 := abs_add_le (((Real.log (vlo c) - Real.log (xlo c)) - (Real.log (vhi c) - Real.log (xhi c))) +
      (Real.log (1 + te) - Plog te)) (Plog te - Plog (tR c))
  have t2 := abs_add_le ((Real.log (vlo c) - Real.log (xlo c)) - (Real.log (vhi c) - Real.log (xhi c)))
      (Real.log (1 + te) - Plog te)
  have t3 := abs_sub (Real.log (vlo c) - Real.log (xlo c)) (Real.log (vhi c) - Real.log (xhi c))
  have : 5 * |te - tR c| ≤ 5 / 2 ^ R2 := by
    have := mul_le_mul_of_nonneg_left s3 (by norm_num : (0 : ℝ) ≤ 5)
    calc _ ≤ 5 * (1 / 2 ^ R2) := this
      _ = _ := by ring
  have s4 : (3 / 100 : ℝ) ^ 6 / (1 - 3 / 100) ≥ 0 := by positivity
  linarith


/-! ### Packed powers of the cell ratios and the `k = 1` moment -/

def NI : ℕ := 6
def Y2 : ℕ := 2 ^ 400 + 1
def trow (m : ℕ × ℕ × ℕ) : ℕ × ℕ := (m.1, ((m.2.1 - m.2.2) * 2 ^ R2) / m.2.2)
def trows : List (ℕ × ℕ) := mrows.map trow
def CT : ℕ := packTot (fun t : ℕ × ℕ => t.1) (fun t => t.2) Y2 NI trows
def Ci (i : ℕ) : ℕ := CT / Y2 ^ i % Y2

def LhatQ : ℚ := ∑ i ∈ Finset.range 5,
  (-1) ^ i / ((i : ℚ) + 1) * ((Ci (i + 1) : ℕ) : ℚ) / 2 ^ (R0 + R2 * (i + 1))

def errL : ℚ := (sumR + lenQ / 2 ^ R0) * eL + 5 * (lenQ / 2 ^ R0)

theorem y2_2 : 2 ≤ Y2 := by
  unfold Y2; have : 1 ≤ 2 ^ 400 := Nat.one_le_two_pow; omega

theorem trows_mem {t : ℕ × ℕ} (h : t ∈ trows) : ∃ c ∈ gasN, t = (rtl c, tau c) := by
  unfold trows mrows at h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
  exact ⟨c, hc, rfl⟩

theorem tau_bounds {c : ℕ × ℕ × ℕ} (h : cellOk c = true) : 1 ≤ tau c ∧ tau c ≤ 2 ^ R2 := by
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hv := (vhat_bounds h2).1
  unfold tau
  constructor
  · rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  · apply Nat.div_le_of_le_mul
    have : (vhat c.1 - vhat c.2.1) * 2 ^ R2 ≤ vhat c.2.1 * 2 ^ R2 := by
      apply Nat.mul_le_mul_right; omega
    nlinarith [this]

theorem trows_sum (f : ℕ × ℕ → ℕ) :
    (trows.map f).sum = (gasN.map fun c => f (rtl c, tau c)).sum := by
  unfold trows mrows; rw [List.map_map, List.map_map]; rfl

theorem Ci_eq (hall : ∀ c ∈ gasN, cellOk c = true)
    (hb : (trows.map fun t => t.1).sum * (2 ^ R2) ^ (NI - 1) < Y2) (i : ℕ) (hi : i < NI) :
    Ci i = (gasN.map fun c => rtl c * tau c ^ i).sum := by
  have hv : ∀ t ∈ trows, 1 ≤ t.2 ∧ t.2 ≤ 2 ^ R2 := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := trows_mem ht
    exact tau_bounds (hall c hc)
  have := digit_gen trows (fun t => t.1) (fun t => t.2) Y2 NI (2 ^ R2) y2_2 hb Nat.one_le_two_pow i hi hv
  unfold Ci CT
  rw [this, trows_sum]

theorem mom_one (hall : ∀ c ∈ gasN, cellOk c = true)
    (hb : (mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB)
    (hb2 : (trows.map fun t => t.1).sum * (2 ^ R2) ^ (NI - 1) < Y2) :
    |(gasN.map (cellTerm 1)).sum - ((LhatQ - psQ 2 / 2 : ℚ) : ℝ)| ≤ ((errL + errPs 2 / 2 : ℚ) : ℝ) := by
  have hR : (0 : ℝ) < 2 ^ R0 := by positivity
  have hQ : (0 : ℝ) < 2 ^ R2 := by positivity
  -- the polynomial sum against the digits
  set g' : ℕ × ℕ × ℕ → ℝ := fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 * Plog (tR c) with hg'
  have hsum : (gasN.map g').sum = (LhatQ : ℝ) := by
    have e1 : ∀ i ∈ Finset.range 5, ((Ci (i + 1) : ℕ) : ℝ) =
        (gasN.map fun c => ((rtl c : ℕ) : ℝ) * ((tau c : ℕ) : ℝ) ^ (i + 1)).sum := by
      intro i hi
      have : i + 1 < NI := by unfold NI; have := Finset.mem_range.1 hi; omega
      rw [Ci_eq hall hb2 (i + 1) this, sum_cast_nat]; push_cast; rfl
    have e2 : ∀ c : ℕ × ℕ × ℕ, g' c = ∑ i ∈ Finset.range 5, (-1 : ℝ) ^ i / ((i : ℝ) + 1) *
        (((rtl c : ℕ) : ℝ) * ((tau c : ℕ) : ℝ) ^ (i + 1)) / 2 ^ (R0 + R2 * (i + 1)) := by
      intro c
      simp only [hg', Plog, tR]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      have q1 : ((tau c : ℕ) : ℝ) ^ (i + 1) / ((2 : ℝ) ^ R2) ^ (i + 1) = ((tau c : ℕ) : ℝ) ^ (i + 1) / 2 ^ (R2 * (i + 1)) := by
        rw [← pow_mul]
      have q2 : (2 : ℝ) ^ (R0 + R2 * (i + 1)) = 2 ^ R0 * 2 ^ (R2 * (i + 1)) := pow_add _ _ _
      rw [div_pow, q1, q2]
      field_simp
    have e3 : (gasN.map g') = gasN.map (fun c => ∑ i ∈ Finset.range 5, (-1 : ℝ) ^ i / ((i : ℝ) + 1) *
        (((rtl c : ℕ) : ℝ) * ((tau c : ℕ) : ℝ) ^ (i + 1)) / 2 ^ (R0 + R2 * (i + 1))) :=
      List.map_congr_left (fun c _ => e2 c)
    rw [e3]
    -- swap the sums
    have swap : ∀ (L : List (ℕ × ℕ × ℕ)) (F : ℕ × ℕ × ℕ → ℕ → ℝ),
        (L.map fun c => ∑ i ∈ Finset.range 5, F c i).sum = ∑ i ∈ Finset.range 5, (L.map fun c => F c i).sum := by
      intro L F
      induction L with
      | nil => simp
      | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
    rw [swap]
    unfold LhatQ
    push_cast
    apply Finset.sum_congr rfl; intro i hi
    have := e1 i hi
    rw [show (gasN.map fun c => (-1 : ℝ) ^ i / ((i : ℝ) + 1) * (((rtl c : ℕ) : ℝ) * ((tau c : ℕ) : ℝ) ^ (i + 1)) /
        2 ^ (R0 + R2 * (i + 1))) = gasN.map (fun c => (((rtl c : ℕ) : ℝ) * ((tau c : ℕ) : ℝ) ^ (i + 1)) *
        ((-1 : ℝ) ^ i / ((i : ℝ) + 1) / 2 ^ (R0 + R2 * (i + 1)))) from
      List.map_congr_left (fun c _ => by ring)]
    rw [List.sum_map_mul_right, ← this]
    ring
  -- per-cell
  have hlen : ∀ c ∈ gasN, |rhoR c * (Real.log (vlo c) - Real.log (vhi c)) - g' c| ≤
      rhoR c * (eL : ℝ) + 5 * (1 / 2 ^ R0) := by
    intro c hc
    obtain ⟨r1, r2, e1, e2, p1, q1, p2, q2, p3, u1, p4, u2, l1, l2, o1, o2⟩ := cell_data (hall c hc)
    obtain ⟨hl, ht0, ht3⟩ := log_cell (hall c hc)
    have hP := Plog_bd ht0 (by linarith)
    have hρ0 : 0 ≤ rhoR c := le_trans (div_nonneg (Nat.cast_nonneg _) hR.le) r1
    have e : rhoR c * (Real.log (vlo c) - Real.log (vhi c)) - g' c =
        rhoR c * ((Real.log (vlo c) - Real.log (vhi c)) - Plog (tR c)) +
        (rhoR c - ((rtl c : ℕ) : ℝ) / 2 ^ R0) * Plog (tR c) := by
      simp only [hg']; ring
    rw [e]
    calc _ ≤ |rhoR c * ((Real.log (vlo c) - Real.log (vhi c)) - Plog (tR c))| +
          |(rhoR c - ((rtl c : ℕ) : ℝ) / 2 ^ R0) * Plog (tR c)| := abs_add_le _ _
      _ = rhoR c * |(Real.log (vlo c) - Real.log (vhi c)) - Plog (tR c)| +
          (rhoR c - ((rtl c : ℕ) : ℝ) / 2 ^ R0) * |Plog (tR c)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hρ0, abs_of_nonneg (sub_nonneg.mpr r1)]
      _ ≤ rhoR c * (eL : ℝ) + (1 / 2 ^ R0) * 5 := by
          apply add_le_add (mul_le_mul_of_nonneg_left hl hρ0)
          exact mul_le_mul (by linarith) hP (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hmain := MomentSource.list_abs_sum_le gasN
    (fun c => rhoR c * (Real.log (vlo c) - Real.log (vhi c))) g'
    (fun c => rhoR c * (eL : ℝ) + 5 * (1 / 2 ^ R0)) hlen
  -- sums of rho
  have hrho : (gasN.map rhoR).sum ≤ (sumR : ℝ) + (lenQ : ℝ) / 2 ^ R0 := by
    have h1 : (gasN.map rhoR).sum ≤ (gasN.map fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0).sum := by
      apply List.sum_le_sum; intro c hc
      exact (cell_data (hall c hc)).2.1.le
    have h2 : (gasN.map fun c => ((rtl c : ℕ) : ℝ) / 2 ^ R0 + 1 / 2 ^ R0).sum =
        (((gasN.map rtl).sum : ℕ) : ℝ) / 2 ^ R0 + gasN.length * (1 / 2 ^ R0) := by
      simp only [div_eq_mul_inv]
      rw [List.sum_map_add, List.sum_map_mul_right, sum_cast_nat]
      have := list_sum_const gasN (1 * ((2 : ℝ) ^ R0)⁻¹)
      simp only [one_mul] at this ⊢
      rw [this]
    rw [h2] at h1
    have hs : (sumR : ℝ) = (((gasN.map rtl).sum : ℕ) : ℝ) / 2 ^ R0 := by
      simp only [sumR, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
    have hl : (lenQ : ℝ) = gasN.length := by simp [lenQ]
    rw [hs, hl]
    have e : (gasN.length : ℝ) / 2 ^ R0 = gasN.length * (1 / 2 ^ R0) := by ring
    rw [e]
    exact h1
  have hl : (lenQ : ℝ) = gasN.length := by simp [lenQ]
  have hE : (gasN.map fun c => rhoR c * (eL : ℝ) + 5 * (1 / 2 ^ R0)).sum ≤ (errL : ℝ) := by
    rw [List.sum_map_add, List.sum_map_mul_right, list_sum_const]
    have e : (errL : ℝ) = ((sumR : ℝ) + (lenQ : ℝ) / 2 ^ R0) * (eL : ℝ) + 5 * ((lenQ : ℝ) / 2 ^ R0) := by
      unfold errL; push_cast; ring
    rw [e]
    have heL : (0 : ℝ) ≤ (eL : ℝ) := by unfold eL; positivity
    have h3 := mul_le_mul_of_nonneg_right hrho heL
    have e2 : (lenQ : ℝ) / 2 ^ R0 = gasN.length * (1 / 2 ^ R0) := by rw [hl]; ring
    rw [e2] at h3 ⊢
    linarith
  -- assemble: closed form of `k = 1`
  have e1 : ∀ c : ℕ × ℕ × ℕ, cellTerm 1 c =
      rhoR c * (Real.log (vlo c) - Real.log (vhi c)) -
      (1 / 2) * (rhoR c * (vlo c ^ 2 - vhi c ^ 2)) := by
    intro c
    unfold cellTerm momK vlo vhi MomentSource.H1
    simp only [ite_true]
    ring
  have e2 : (gasN.map (cellTerm 1)).sum = (gasN.map fun c => rhoR c * (Real.log (vlo c) - Real.log (vhi c))).sum -
      (1 / 2) * psTrue 2 := by
    rw [List.map_congr_left (fun c _ => e1 c), list_sum_sub, List.sum_map_mul_left]
    rfl
  have hps := ps_err hall hb 2 (by unfold NJ; omega)
  have e3 : ((LhatQ - psQ 2 / 2 : ℚ) : ℝ) = (LhatQ : ℝ) - (1 / 2) * (psQ 2 : ℝ) := by push_cast; ring
  have e4 : ((errL + errPs 2 / 2 : ℚ) : ℝ) = (errL : ℝ) + (1 / 2) * (errPs 2 : ℝ) := by push_cast; ring
  rw [e2, e3, e4, ← hsum]
  have f : (gasN.map fun c => rhoR c * (Real.log (vlo c) - Real.log (vhi c))).sum - 1 / 2 * psTrue 2 -
      ((gasN.map g').sum - 1 / 2 * (psQ 2 : ℝ)) =
      ((gasN.map fun c => rhoR c * (Real.log (vlo c) - Real.log (vhi c))).sum - (gasN.map g').sum) -
      (1 / 2) * (psTrue 2 - psQ 2) := by ring
  rw [f]
  calc _ ≤ |(gasN.map fun c => rhoR c * (Real.log (vlo c) - Real.log (vhi c))).sum - (gasN.map g').sum| +
        |(1 / 2 : ℝ) * (psTrue 2 - psQ 2)| := abs_sub _ _
    _ ≤ (errL : ℝ) + (1 / 2) * (errPs 2 : ℝ) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact add_le_add (hmain.trans hE) (mul_le_mul_of_nonneg_left hps (by norm_num))


/-! ### The moment check -/

def momCheck (k : ℕ) : Bool :=
  if k = 1 then decide (|LhatQ - psQ 2 / 2 - muL.getD 1 0| + (errL + errPs 2 / 2) ≤ 1 / 10000)
  else decide (|momQ k - muL.getD k 0| + momErr k ≤ 1 / 10000)

def momKernel : Bool :=
  gasN.all cellOk &&
  decide ((mrows.map fun m => m.1).sum * (2 ^ PM) ^ (NJ - 1) < YB) &&
  decide ((trows.map fun t => t.1).sum * (2 ^ R2) ^ (NI - 1) < Y2) &&
  (List.range 32).all fun i => momCheck (i + 1)

set_option maxRecDepth 100000 in
theorem momKernel_true : momKernel = true := by
  -- kcost: 3.5 s measured 6 Nov (427 cells: 2 isqrt each, 4 packed geometric sums, 34 digits, 32 rational checks)
  decide +kernel

theorem moment_all (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 32) :
    |(gasN.map (cellTerm k)).sum - ((muL.getD k 0 : ℚ) : ℝ)| ≤ 1 / 10000 := by
  have hK := momKernel_true
  unfold momKernel at hK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hK
  obtain ⟨⟨⟨hall', hb⟩, hb2⟩, hchk⟩ := hK
  have hall : ∀ c ∈ gasN, cellOk c = true := fun c hc => by simpa using hall' c hc
  have hc := hchk (k - 1) (by omega)
  have hkk : k - 1 + 1 = k := by omega
  rw [hkk] at hc
  unfold momCheck at hc
  by_cases h1 : k = 1
  · subst h1
    simp only [ite_true, decide_eq_true_eq] at hc
    have h := mom_one hall hb hb2
    have hc' : (|LhatQ - psQ 2 / 2 - muL.getD 1 0| : ℝ) + ((errL + errPs 2 / 2 : ℚ) : ℝ) ≤ 1 / 10000 := by
      have := (Rat.cast_le (K := ℝ)).2 hc
      push_cast at this ⊢
      exact this
    have e : (gasN.map (cellTerm 1)).sum - ((muL.getD 1 0 : ℚ) : ℝ) =
        ((gasN.map (cellTerm 1)).sum - ((LhatQ - psQ 2 / 2 : ℚ) : ℝ)) +
        (((LhatQ - psQ 2 / 2 : ℚ) : ℝ) - ((muL.getD 1 0 : ℚ) : ℝ)) := by ring
    rw [e]
    have t := abs_add_le ((gasN.map (cellTerm 1)).sum - ((LhatQ - psQ 2 / 2 : ℚ) : ℝ))
      (((LhatQ - psQ 2 / 2 : ℚ) : ℝ) - ((muL.getD 1 0 : ℚ) : ℝ))
    have e2 : |(((LhatQ - psQ 2 / 2 : ℚ) : ℝ) - ((muL.getD 1 0 : ℚ) : ℝ))| =
        (|LhatQ - psQ 2 / 2 - muL.getD 1 0| : ℝ) := by
      push_cast; rfl
    linarith
  · simp only [h1, ite_false, decide_eq_true_eq] at hc
    have h := mom_ge2 hall hb k (by omega) (by unfold NJ; omega)
    have hc' : (|momQ k - muL.getD k 0| : ℝ) + (momErr k : ℝ) ≤ 1 / 10000 := by
      have := (Rat.cast_le (K := ℝ)).2 hc
      push_cast at this ⊢
      exact this
    have e : (gasN.map (cellTerm k)).sum - ((muL.getD k 0 : ℚ) : ℝ) =
        ((gasN.map (cellTerm k)).sum - (momQ k : ℝ)) + ((momQ k : ℝ) - ((muL.getD k 0 : ℚ) : ℝ)) := by ring
    rw [e]
    have t := abs_add_le ((gasN.map (cellTerm k)).sum - (momQ k : ℝ)) ((momQ k : ℝ) - ((muL.getD k 0 : ℚ) : ℝ))
    have e2 : |((momQ k : ℝ) - ((muL.getD k 0 : ℚ) : ℝ))| = (|momQ k - muL.getD k 0| : ℝ) := by
      push_cast; rfl
    linarith

theorem near_moment (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 32) :
    |((capSource.gas Sign.pos).map fun c => c.w / (c.hi - c.lo) *
        (momK k (vY c.lo) - momK k (vY c.hi))).sum - (muL.getD k 0 : ℚ)| ≤ 1 / 10000 := by
  rw [gas_conv]
  exact moment_all k hk1 hk2

section
open Complex
/-! ### Complex Taylor facts -/

theorem tay8 (θ : ℝ) :
    ∑ m ∈ Finset.range 8, ((I * (θ : ℂ)) ^ m / (m.factorial : ℂ)) =
      ((1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 : ℝ) : ℂ) +
      ((θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 : ℝ) : ℂ) * I := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow, I_sq, pow_zero]
  push_cast
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  simp only [pow_zero, pow_one, I_sq, h3]
  ring

theorem exp_I_err (x y : ℝ) : ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| := by
  have : Complex.exp (I * x) - Complex.exp (I * y) = Complex.exp (I * y) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul]
  have h1 : ‖Complex.exp (I * y)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I y
  rw [h1, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  calc 2 * |Real.sin ((x - y) / 2)| ≤ 2 * |(x - y) / 2| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |x - y| := by rw [abs_div]; simp; ring

/-! ### The rotation `exp (i π / 93)` -/

def GA : ℤ := 281314392683385
def GB : ℤ := 9506575800072
def Q0 : ℕ := 48

noncomputable def wT : ℂ := Complex.exp (I * ((Real.pi / 93 : ℝ) : ℂ))
noncomputable def wH : ℂ := ((GA : ℂ) + (GB : ℂ) * I) / (2 : ℂ) ^ Q0

def tayB (x : ℚ) (n : ℕ) : ℚ := x ^ n * (((n : ℚ) + 1) / ((n.factorial : ℚ) * n))
def thc : ℚ := 314159265358979323846 / (10 ^ 20 * 93)
def tayRe (θ : ℚ) : ℚ := 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720
def tayIm (θ : ℚ) : ℚ := θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040
def dw : ℚ := 1 / (93 * 10 ^ 20) + tayB thc 8 + 2 / 2 ^ (Q0 + 1)

theorem GA_close : |(GA : ℚ) / 2 ^ Q0 - tayRe thc| ≤ 1 / 2 ^ (Q0 + 1) := by
  unfold GA Q0 tayRe thc; rw [abs_le]; constructor <;> norm_num

theorem GB_close : |(GB : ℚ) / 2 ^ Q0 - tayIm thc| ≤ 1 / 2 ^ (Q0 + 1) := by
  unfold GB Q0 tayIm thc; rw [abs_le]; constructor <;> norm_num

theorem wH_close : ‖wH - wT‖ ≤ (dw : ℝ) := by
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  set θ : ℝ := Real.pi / 93 with hθ
  have hthc : (thc : ℝ) = 314159265358979323846 / (10 ^ 20 * 93) := by unfold thc; push_cast; norm_num
  have hθ1 : (thc : ℝ) ≤ θ := by
    rw [hthc, hθ, div_le_div_iff₀ (by norm_num) (by norm_num)]; norm_num at hpi1 ⊢; linarith
  have hθ2 : θ ≤ thc + 1 / (93 * 10 ^ 20) := by
    rw [hthc, hθ, div_add_div _ _ (by norm_num) (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]
    norm_num at hpi2 ⊢; linarith
  have hθc0 : (0 : ℝ) ≤ thc := by rw [hthc]; norm_num
  have hθc1 : (thc : ℝ) ≤ 1 := by rw [hthc]; norm_num
  -- step 1
  have s1 : ‖wT - Complex.exp (I * ((thc : ℝ) : ℂ))‖ ≤ 1 / (93 * 10 ^ 20) := by
    unfold wT
    refine (exp_I_err θ (thc : ℝ)).trans ?_
    rw [abs_le]; constructor <;> linarith
  -- step 2
  have s2 : ‖Complex.exp (I * ((thc : ℝ) : ℂ)) - ∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))‖
      ≤ (tayB thc 8 : ℝ) := by
    have hn : ‖I * ((thc : ℝ) : ℂ)‖ = thc := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθc0, one_mul]
    have := Complex.exp_bound (x := I * ((thc : ℝ) : ℂ)) (by rw [hn]; exact hθc1) (n := 8) (by norm_num)
    rw [hn] at this
    refine this.trans (le_of_eq ?_)
    unfold tayB; push_cast; norm_num [Nat.factorial]
  -- step 3
  have s3 : ‖(∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) - wH‖ ≤ 2 / 2 ^ (Q0 + 1) := by
    rw [tay8]
    have hwH : wH = (((GA : ℝ) / 2 ^ Q0 : ℝ) : ℂ) + (((GB : ℝ) / 2 ^ Q0 : ℝ) : ℂ) * I := by
      unfold wH; push_cast; ring
    rw [hwH]
    have e : (((1 - (thc : ℝ) ^ 2 / 2 + (thc : ℝ) ^ 4 / 24 - (thc : ℝ) ^ 6 / 720 : ℝ) : ℂ) +
        (((thc : ℝ) - (thc : ℝ) ^ 3 / 6 + (thc : ℝ) ^ 5 / 120 - (thc : ℝ) ^ 7 / 5040 : ℝ) : ℂ) * I) -
        ((((GA : ℝ) / 2 ^ Q0 : ℝ) : ℂ) + (((GB : ℝ) / 2 ^ Q0 : ℝ) : ℂ) * I) =
        ((((tayRe thc : ℚ) : ℝ) - (GA : ℝ) / 2 ^ Q0 : ℝ) : ℂ) +
        ((((tayIm thc : ℚ) : ℝ) - (GB : ℝ) / 2 ^ Q0 : ℝ) : ℂ) * I := by
      unfold tayRe tayIm; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have ga := GA_close
    have gb := GB_close
    have ga' : |(((tayRe thc : ℚ) : ℝ) - (GA : ℝ) / 2 ^ Q0)| ≤ 1 / 2 ^ (Q0 + 1) := by
      have := (Rat.cast_le (K := ℝ)).2 (abs_le.1 ga).1
      have h2 := (Rat.cast_le (K := ℝ)).2 (abs_le.1 ga).2
      push_cast at this h2
      rw [abs_le]; constructor <;> linarith
    have gb' : |(((tayIm thc : ℚ) : ℝ) - (GB : ℝ) / 2 ^ Q0)| ≤ 1 / 2 ^ (Q0 + 1) := by
      have := (Rat.cast_le (K := ℝ)).2 (abs_le.1 gb).1
      have h2 := (Rat.cast_le (K := ℝ)).2 (abs_le.1 gb).2
      push_cast at this h2
      rw [abs_le]; constructor <;> linarith
    linarith [ga', gb', show (2 : ℝ) / 2 ^ (Q0 + 1) = 1 / 2 ^ (Q0 + 1) + 1 / 2 ^ (Q0 + 1) by ring]
  have key : wH - wT = -(wT - Complex.exp (I * ((thc : ℝ) : ℂ))) -
      (Complex.exp (I * ((thc : ℝ) : ℂ)) - ∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) -
      ((∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) - wH) := by ring
  rw [key]
  have t1 := norm_sub_le (-(wT - Complex.exp (I * ((thc : ℝ) : ℂ))) -
      (Complex.exp (I * ((thc : ℝ) : ℂ)) - ∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))))
      ((∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ))) - wH)
  have t2 := norm_sub_le (-(wT - Complex.exp (I * ((thc : ℝ) : ℂ))))
      (Complex.exp (I * ((thc : ℝ) : ℂ)) - ∑ m ∈ Finset.range 8, ((I * ((thc : ℝ) : ℂ)) ^ m / (m.factorial : ℂ)))
  rw [norm_neg] at t2
  have hd : (dw : ℝ) = 1 / (93 * 10 ^ 20) + (tayB thc 8 : ℝ) + 2 / 2 ^ (Q0 + 1) := by
    unfold dw; push_cast; ring
  rw [hd]
  linarith

theorem cpow_err (a b : ℂ) (B : ℝ) (hB1 : 1 ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ m * ‖a - b‖ * B ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + b ^ m * (a - b) := by ring
    rw [e]
    have hBm : 1 ≤ B ^ m := one_le_pow₀ hB1
    have hBm1 : B ^ m ≤ B ^ (m + 1) := pow_le_pow_right₀ hB1 (by omega)
    have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
    calc _ ≤ ‖a * (a ^ m - b ^ m)‖ + ‖b ^ m * (a - b)‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ m - b ^ m‖ + ‖b‖ ^ m * ‖a - b‖ := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ B * (m * ‖a - b‖ * B ^ m) + B ^ m * ‖a - b‖ := by
          apply add_le_add
          · exact mul_le_mul ha ih (norm_nonneg _) (by linarith)
          · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb m) h0
      _ ≤ ((m + 1 : ℕ) : ℝ) * ‖a - b‖ * B ^ (m + 1) := by
          push_cast
          have : B * (m * ‖a - b‖ * B ^ m) = m * ‖a - b‖ * B ^ (m + 1) := by ring
          rw [this]
          nlinarith [mul_nonneg h0 (Nat.cast_nonneg m : (0:ℝ) ≤ m), mul_le_mul_of_nonneg_left hBm1 h0]

def gpow : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((gpow m).1 * GA - (gpow m).2 * GB, (gpow m).1 * GB + (gpow m).2 * GA)

theorem gpow_eq (m : ℕ) : (((gpow m).1 : ℤ) : ℂ) + (((gpow m).2 : ℤ) : ℂ) * I = ((GA : ℂ) + (GB : ℂ) * I) ^ m := by
  induction m with
  | zero => simp [gpow]
  | succ m ih =>
    rw [pow_succ, ← ih]
    simp only [gpow]
    push_cast
    ring_nf
    rw [I_sq]; ring

theorem wH_pow_re (m : ℕ) : (wH ^ m).re = ((gpow m).1 : ℝ) / 2 ^ (Q0 * m) := by
  have : wH ^ m = (((((gpow m).1 : ℝ) / 2 ^ (Q0 * m) : ℝ)) : ℂ) + (((gpow m).2 : ℝ) / 2 ^ (Q0 * m) : ℝ) * I := by
    unfold wH
    rw [div_pow, ← gpow_eq, ← pow_mul]
    push_cast
    ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem wT_pow_re (m : ℕ) : (wT ^ m).re = Real.cos (m * Real.pi / 93) := by
  unfold wT
  rw [← Complex.exp_nat_mul]
  have : (m : ℂ) * (I * ((Real.pi / 93 : ℝ) : ℂ)) = ((m * Real.pi / 93 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem dw_le : dw ≤ 4 / 10 ^ 15 := by
  unfold dw tayB thc Q0; norm_num [Nat.factorial]

theorem cos_err (m : ℕ) (hm : m ≤ 185) :
    |((gpow m).1 : ℝ) / 2 ^ (Q0 * m) - Real.cos (m * Real.pi / 93)| ≤ 8 / 10 ^ 13 ∧
    |((gpow m).1 : ℝ) / 2 ^ (Q0 * m)| ≤ 11 / 10 := by
  have hdw : (dw : ℝ) ≤ 4 / 10 ^ 15 := by
    have := (Rat.cast_le (K := ℝ)).2 dw_le
    push_cast at this
    exact this
  have hdw0 : (0 : ℝ) ≤ dw := by unfold dw tayB thc; positivity
  set B : ℝ := 1 + 4 / 10 ^ 15 with hB
  have hB1 : 1 ≤ B := by rw [hB]; norm_num
  have hwT : ‖wT‖ = 1 := by
    unfold wT; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hwH : ‖wH‖ ≤ B := by
    have := wH_close
    have : ‖wH‖ ≤ ‖wT‖ + ‖wH - wT‖ := by
      calc ‖wH‖ = ‖wT + (wH - wT)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [hB]; linarith [wH_close]
  have hwT' : ‖wT‖ ≤ B := by rw [hwT]; exact hB1
  have h := cpow_err wH wT B hB1 hwH hwT' m
  have hBm : B ^ m ≤ B ^ 185 := pow_le_pow_right₀ hB1 hm
  have hB185 : B ^ 185 ≤ 1001 / 1000 := by rw [hB]; norm_num
  have hre : |(wH ^ m).re - (wT ^ m).re| ≤ ‖wH ^ m - wT ^ m‖ := by
    have := Complex.abs_re_le_norm (wH ^ m - wT ^ m)
    simpa using this
  rw [wH_pow_re, wT_pow_re] at hre
  constructor
  · refine hre.trans (h.trans ?_)
    have hmm : (m : ℝ) ≤ 185 := by exact_mod_cast hm
    have hn : ‖wH - wT‖ ≤ 4 / 10 ^ 15 := (wH_close).trans hdw
    calc (m : ℝ) * ‖wH - wT‖ * B ^ m ≤ 185 * (4 / 10 ^ 15) * (1001 / 1000) := by
          apply mul_le_mul (mul_le_mul hmm hn (norm_nonneg _) (by norm_num)) (hBm.trans hB185)
            (by positivity) (by norm_num)
      _ ≤ 8 / 10 ^ 13 := by norm_num
  · have h1 : |(wH ^ m).re| ≤ ‖wH ^ m‖ := by simpa using Complex.abs_re_le_norm (wH ^ m)
    rw [wH_pow_re] at h1
    refine h1.trans ?_
    rw [norm_pow]
    calc ‖wH‖ ^ m ≤ B ^ m := pow_le_pow_left₀ (norm_nonneg _) hwH m
      _ ≤ 11 / 10 := hBm.trans (hB185.trans (by norm_num))

/-! ### The cosine table -/

def FB : ℕ := 40
def uOf (m : ℕ) (x : ℤ) : ℕ := (x * 2 ^ FB / 2 ^ (Q0 * m) + 2 ^ (FB + 1)).toNat

def tabPack : ℕ → ℤ → ℤ → ℕ → ℕ
  | _, _, _, 0 => 0
  | m, x, y, n + 1 => uOf m x + 2 ^ 64 * tabPack (m + 1) (x * GA - y * GB) (x * GB + y * GA) n

def TC : ℕ := tabPack 0 1 0 186
def uTab (m : ℕ) : ℕ := TC / (2 ^ 64) ^ m % 2 ^ 64

theorem tabPack_spec : ∀ (n m : ℕ), tabPack m (gpow m).1 (gpow m).2 n =
    ∑ i ∈ Finset.range n, uOf (m + i) (gpow (m + i)).1 * (2 ^ 64) ^ i := by
  intro n
  induction n with
  | zero => intro m; simp [tabPack]
  | succ n ih =>
    intro m
    rw [Finset.sum_range_succ', tabPack]
    have := ih (m + 1)
    have e : tabPack (m + 1) ((gpow m).1 * GA - (gpow m).2 * GB) ((gpow m).1 * GB + (gpow m).2 * GA) n =
        tabPack (m + 1) (gpow (m + 1)).1 (gpow (m + 1)).2 n := rfl
    rw [e, this, Finset.mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [pow_succ, show m + 1 + i = m + (i + 1) by ring]; ring

theorem u_spec (m : ℕ) (hm : m ≤ 185) :
    uOf m (gpow m).1 < 2 ^ (FB + 2) ∧
    |((uOf m (gpow m).1 : ℕ) - (2 : ℝ) ^ (FB + 1)) / 2 ^ FB - Real.cos (m * Real.pi / 93)| ≤
      1 / 2 ^ FB + 8 / 10 ^ 13 := by
  obtain ⟨hce, hbd⟩ := cos_err m hm
  set X : ℤ := (gpow m).1 with hX
  have hD : (0 : ℤ) < 2 ^ (Q0 * m) := by positivity
  set z : ℤ := X * 2 ^ FB / 2 ^ (Q0 * m) with hz
  have hz1 : z * 2 ^ (Q0 * m) ≤ X * 2 ^ FB := Int.ediv_mul_le _ hD.ne'
  have hz2 : X * 2 ^ FB < (z + 1) * 2 ^ (Q0 * m) := Int.lt_ediv_add_one_mul_self _ hD
  have hDR : (0 : ℝ) < 2 ^ (Q0 * m) := by positivity
  have hF : (0 : ℝ) < 2 ^ FB := by positivity
  have hz1R : (z : ℝ) * 2 ^ (Q0 * m) ≤ X * 2 ^ FB := by exact_mod_cast hz1
  have hz2R : (X : ℝ) * 2 ^ FB < ((z : ℝ) + 1) * 2 ^ (Q0 * m) := by exact_mod_cast hz2
  set R : ℝ := (X : ℝ) / 2 ^ (Q0 * m) with hR
  have hRz1 : (z : ℝ) / 2 ^ FB ≤ R := by
    rw [hR, div_le_div_iff₀ hF hDR]; linarith
  have hRz2 : R < (z : ℝ) / 2 ^ FB + 1 / 2 ^ FB := by
    rw [hR, ← add_div, div_lt_div_iff₀ hDR hF]; linarith
  have hRb : |R| ≤ 11 / 10 := hbd
  have hFv : (2 : ℝ) ^ FB = 1099511627776 := by unfold FB; norm_num
  have hF1 : (1 : ℝ) / 2 ^ FB ≤ 1 / 10 ^ 12 := by rw [hFv]; norm_num
  have hlow : -(2 : ℝ) ^ (FB + 1) < z := by
    have : (z : ℝ) / 2 ^ FB + 1 / 2 ^ FB > -11 / 10 := by
      have := (abs_le.1 hRb).1; linarith
    have h2 : (2 : ℝ) ^ (FB + 1) = 2 * 2 ^ FB := by ring
    rw [h2]
    have h3 : (z : ℝ) + 1 > -11 / 10 * 2 ^ FB := by
      have := mul_lt_mul_of_pos_right this hF
      rw [add_mul, div_mul_cancel₀ _ hF.ne', div_mul_cancel₀ _ hF.ne'] at this; linarith
    rw [hFv] at h3 ⊢; linarith
  have hhigh : (z : ℝ) ≤ 11 / 10 * 2 ^ FB := by
    have := (abs_le.1 hRb).2
    have := mul_le_mul_of_nonneg_right (hRz1.trans this) hF.le
    rw [div_mul_cancel₀ _ hF.ne'] at this; exact this
  have hlowZ : -(2 : ℤ) ^ (FB + 1) < z := by exact_mod_cast hlow
  have hnn : 0 ≤ z + 2 ^ (FB + 1) := by linarith
  have hu : ((uOf m X : ℕ) : ℤ) = z + 2 ^ (FB + 1) := by
    unfold uOf; rw [Int.toNat_of_nonneg hnn]
  have huR : ((uOf m X : ℕ) : ℝ) = (z : ℝ) + 2 ^ (FB + 1) := by
    have := congrArg (fun t : ℤ => (t : ℝ)) hu
    simpa using this
  constructor
  · have : ((uOf m X : ℕ) : ℝ) < 2 ^ (FB + 2) := by
      rw [huR]
      have h2 : (2 : ℝ) ^ (FB + 1) = 2 * 2 ^ FB := by ring
      have h3 : (2 : ℝ) ^ (FB + 2) = 4 * 2 ^ FB := by ring
      rw [h2, h3]; rw [hFv] at hhigh ⊢; norm_num at hhigh ⊢; linarith
    exact_mod_cast this
  · rw [huR]
    have e : ((z : ℝ) + 2 ^ (FB + 1) - 2 ^ (FB + 1)) / 2 ^ FB = (z : ℝ) / 2 ^ FB := by ring
    rw [e]
    rw [abs_le] at hce ⊢
    constructor <;> linarith [hce.1, hce.2]

theorem uTab_eq (m : ℕ) (hm : m < 186) : uTab m = uOf m (gpow m).1 := by
  have hb : ∀ i < 186, uOf (0 + i) (gpow (0 + i)).1 < 2 ^ 64 := fun i hi => by
    have := (u_spec i (by omega)).1
    have h42 : (2 : ℕ) ^ (FB + 2) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by unfold FB; norm_num)
    simpa using lt_of_lt_of_le this h42
  have := digit_sum (2 ^ 64) (by positivity) 186 (fun i => uOf (0 + i) (gpow (0 + i)).1) hb m hm
  unfold uTab TC
  have h0 : (tabPack 0 1 0 186) = tabPack 0 (gpow 0).1 (gpow 0).2 186 := rfl
  rw [h0, tabPack_spec]
  simpa using this
end

/-! ### Exponential enclosures -/

def expQ (x : ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℚ)

theorem exp_enc (x : ℚ) (n : ℕ) (hn : 0 < n) (hx : |(x : ℝ)| ≤ 1) :
    |Real.exp (x : ℝ) - (expQ x n : ℝ)| ≤ (tayB |x| n : ℝ) := by
  have h := Real.exp_bound hx hn
  have e : (expQ x n : ℝ) = ∑ m ∈ Finset.range n, (x : ℝ) ^ m / (m.factorial : ℝ) := by
    unfold expQ; push_cast; rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  unfold tayB; push_cast
  ring

/-- The quarter-argument exponential used for the radii. -/
def ehat (s : ℚ) : ℚ := expQ (-s / 4) 20

theorem tayB_mono {x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) : tayB x n ≤ tayB y n := by
  unfold tayB
  have h : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy n
  have h2 : (0 : ℚ) ≤ ((n : ℚ) + 1) / ((n.factorial : ℚ) * n) := by positivity
  exact mul_le_mul_of_nonneg_right h h2

theorem rad_enc (s : ℚ) (hs0 : 0 ≤ s) (hs : s ≤ 4 * (49 / 50))
    (hh1 : ehat s ≤ 1) (hh0 : 0 ≤ ehat s) :
    |Real.exp (-(s : ℝ)) - ((ehat s) ^ 4 : ℚ)| ≤ 4 * (tayB (49 / 50) 20 : ℝ) := by
  have hsR : (s : ℝ) ≤ 4 * (49 / 50) := by
    have := (Rat.cast_le (K := ℝ)).2 hs
    push_cast at this; linarith
  have hs0R : (0 : ℝ) ≤ s := Rat.cast_nonneg.2 hs0
  have hx : |((-s / 4 : ℚ) : ℝ)| ≤ 1 := by
    push_cast
    rw [abs_le]; constructor <;> linarith
  have h := exp_enc (-s / 4) 20 (by norm_num) hx
  have habs : |(-s / 4 : ℚ)| ≤ 49 / 50 := by
    rw [abs_le]; constructor <;> linarith
  have hb : (tayB |(-s / 4 : ℚ)| 20 : ℝ) ≤ (tayB (49 / 50) 20 : ℝ) := by
    exact (Rat.cast_le (K := ℝ)).2 (tayB_mono (abs_nonneg _) habs 20)
  have hxe : Real.exp (-(s : ℝ)) = (Real.exp (((-s / 4 : ℚ) : ℝ))) ^ 4 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h1 : (0 : ℝ) ≤ ((ehat s : ℚ) : ℝ) := Rat.cast_nonneg.2 hh0
  have h2 : ((ehat s : ℚ) : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).2 hh1
    simpa using this
  have h3 : Real.exp (((-s / 4 : ℚ) : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; push_cast
    linarith
  have h4 := CatalanMeasure.GenD.Signed.RouteI.MomentInputs.abs_pow_sub_pow_le_unit (Real.exp_pos _).le h3 h1 h2 4
  rw [hxe]
  have : ((ehat s ^ 4 : ℚ) : ℝ) = ((ehat s : ℚ) : ℝ) ^ 4 := by push_cast; rfl
  rw [this]
  refine h4.trans ?_
  have h' : |Real.exp (((-s / 4 : ℚ) : ℝ)) - ((ehat s : ℚ) : ℝ)| ≤ (tayB (49 / 50) 20 : ℝ) := by
    have e2 : ((ehat s : ℚ) : ℝ) = (expQ (-s / 4) 20 : ℝ) := rfl
    rw [e2]; exact h.trans hb
  have h44 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [h44]
  exact mul_le_mul_of_nonneg_left h' (by norm_num)

/-! ### Strength and curvature as functions of `r = q²` -/

def fS (r : ℚ) : ℚ := 3 * (1 - r ^ 2) / (2 * (1 + 4 * r + r ^ 2))
def fC (r : ℚ) : ℚ := (1 - r) ^ 2 / (2 * (1 + 4 * r + r ^ 2))

theorem fS_lip {r r' : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (h0' : 0 ≤ r') (h1' : r' ≤ 1) :
    |3 * (1 - r ^ 2) / (2 * (1 + 4 * r + r ^ 2)) - 3 * (1 - r' ^ 2) / (2 * (1 + 4 * r' + r' ^ 2))| ≤
      18 * |r - r'| := by
  have hD : 0 < 2 * (1 + 4 * r + r ^ 2) := by positivity
  have hD' : 0 < 2 * (1 + 4 * r' + r' ^ 2) := by positivity
  rw [div_sub_div _ _ hD.ne' hD'.ne']
  have e : 3 * (1 - r ^ 2) * (2 * (1 + 4 * r' + r' ^ 2)) - 2 * (1 + 4 * r + r ^ 2) * (3 * (1 - r' ^ 2)) =
      6 * (r' - r) * (4 + 2 * (r + r') + 4 * r * r') := by ring
  rw [e, abs_div, abs_of_pos (mul_pos hD hD'), abs_mul, abs_mul]
  rw [div_le_iff₀ (mul_pos hD hD')]
  have h6 : |(6 : ℝ)| = 6 := abs_of_pos (by norm_num)
  have hq : |4 + 2 * (r + r') + 4 * r * r'| ≤ 12 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul h1 h1' h0' zero_le_one]
  have hr : |r' - r| = |r - r'| := abs_sub_comm _ _
  rw [h6, hr]
  have hDD : 4 ≤ 2 * (1 + 4 * r + r ^ 2) * (2 * (1 + 4 * r' + r' ^ 2)) := by
    nlinarith [sq_nonneg r, sq_nonneg r', mul_nonneg h0 h0']
  have h0a : 0 ≤ |r - r'| := abs_nonneg _
  calc 6 * |r - r'| * |4 + 2 * (r + r') + 4 * r * r'| ≤ 6 * |r - r'| * 12 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 72 * |r - r'| := by ring
    _ ≤ 18 * |r - r'| * (2 * (1 + 4 * r + r ^ 2) * (2 * (1 + 4 * r' + r' ^ 2))) := by
        nlinarith [mul_le_mul_of_nonneg_left hDD (by positivity : (0 : ℝ) ≤ 18 * |r - r'|)]

theorem fC_lip {r r' : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (h0' : 0 ≤ r') (h1' : r' ≤ 1) :
    |(1 - r) ^ 2 / (2 * (1 + 4 * r + r ^ 2)) - (1 - r') ^ 2 / (2 * (1 + 4 * r' + r' ^ 2))| ≤
      3 * |r - r'| := by
  have hD : 0 < 2 * (1 + 4 * r + r ^ 2) := by positivity
  have hD' : 0 < 2 * (1 + 4 * r' + r' ^ 2) := by positivity
  rw [div_sub_div _ _ hD.ne' hD'.ne']
  have e : (1 - r) ^ 2 * (2 * (1 + 4 * r' + r' ^ 2)) - 2 * (1 + 4 * r + r ^ 2) * (1 - r') ^ 2 =
      12 * (r' - r) * (1 - r * r') := by ring
  rw [e, abs_div, abs_of_pos (mul_pos hD hD'), abs_mul, abs_mul]
  rw [div_le_iff₀ (mul_pos hD hD')]
  have h6 : |(12 : ℝ)| = 12 := abs_of_pos (by norm_num)
  have hq : |1 - r * r'| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0', mul_le_mul h1 h1' h0' zero_le_one]
  have hr : |r' - r| = |r - r'| := abs_sub_comm _ _
  rw [h6, hr]
  have hDD : 4 ≤ 2 * (1 + 4 * r + r ^ 2) * (2 * (1 + 4 * r' + r' ^ 2)) := by
    nlinarith [sq_nonneg r, sq_nonneg r', mul_nonneg h0 h0']
  have h0a : 0 ≤ |r - r'| := abs_nonneg _
  calc 12 * |r - r'| * |1 - r * r'| ≤ 12 * |r - r'| * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 12 * |r - r'| := by ring
    _ ≤ 3 * |r - r'| * (2 * (1 + 4 * r + r ^ 2) * (2 * (1 + 4 * r' + r' ^ 2))) := by
        nlinarith [mul_le_mul_of_nonneg_left hDD (by positivity : (0 : ℝ) ≤ 3 * |r - r'|)]


/-! ### The radial sum over the auxiliary entries -/

def paN : List (ℕ × ℕ × ℕ) := paT.map fun t => (t.1.toNat, t.2.1.toNat, t.2.2.toNat)
def MM : ℕ := (sumP paT).toNat

theorem paT_range : ∀ t ∈ paT, 0 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ t.2.1 ≤ 93 := by
  -- kcost: 0.05 s estimated (680 triples, 3 comparisons each)
  decide +kernel

theorem MM_real : (MM : ℝ) = (sumP paT : ℝ) := by
  unfold MM
  have h : (0 : ℤ) ≤ sumP paT := pa_tot.le
  exact_mod_cast Int.toNat_of_nonneg h

theorem mkAux_fields {g : ℝ} {M : ℤ} {t : Tr} (hv : 0 ≤ t.2.2) (hM : 0 ≤ M) (hg : 0 ≤ g) :
    (mkAux g M t).rad = t.1.toNat ∧ (mkAux g M t).phase = Real.pi * (t.2.1 : ℝ) / 93 ∧
      (mkAux g M t).w = g * (t.2.2 : ℝ) / (M : ℝ) := by
  unfold mkAux
  rw [dif_pos ⟨hv, hM, hg⟩]
  exact ⟨rfl, rfl, rfl⟩

noncomputable def radTerm (k : ℕ) (e : ℕ × ℕ × ℕ) : ℝ :=
  (tgt Sign.pos * (e.2.2 : ℝ) / MM) *
    (capSource.coef k * capSource.rad e.1 ^ k * Real.cos ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93)))

theorem radCoef_conv (k : ℕ) : radCoef capSource k = (paN.map (radTerm k)).sum := by
  show ((paT.map (mkAux (tgt Sign.pos) (sumP paT))).map _).sum = _
  rw [List.map_map]
  unfold paN
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro t ht
  obtain ⟨h0, h1, h2⟩ := paT_range t ht
  obtain ⟨hr, hp, hw⟩ := mkAux_fields (g := tgt Sign.pos) (M := sumP paT) (pa_ok t ht).1 pa_tot.le
    (tgt_nonneg Sign.pos)
  simp only [Function.comp]
  rw [hr, hp, hw]
  unfold radTerm
  have e1 : ((t.2.1.toNat : ℕ) : ℝ) = (t.2.1 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h1
  have e2 : ((t.2.2.toNat : ℕ) : ℝ) = (t.2.2 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (pa_ok t ht).1
  simp only [e1, e2, MM_real]

/-- `(1 + S k + C k²) / k` with the strength and curvature of the source -/
noncomputable def cK (k : ℕ) : ℝ :=
  (1 + capSource.strength * k + capSource.curvature * (k : ℝ) ^ 2) / k

noncomputable def zTerm (k : ℕ) (e : ℕ × ℕ × ℕ) : ℝ :=
  (e.2.2 : ℝ) * (capSource.q * capSource.rad e.1) ^ k * Real.cos ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93))

noncomputable def Ztrue (k : ℕ) : ℝ := (paN.map (zTerm k)).sum

theorem radCoef_form (k : ℕ) :
    radCoef capSource k = -(tgt Sign.pos / MM) * cK k * Ztrue k := by
  rw [radCoef_conv]
  unfold Ztrue
  have hterm : ∀ e : ℕ × ℕ × ℕ, radTerm k e = (-(tgt Sign.pos / MM) * cK k) * zTerm k e := by
    intro e
    unfold radTerm zTerm cK CapSource.coef
    rw [mul_pow]
    ring
  rw [List.map_congr_left (fun e _ => hterm e), List.sum_map_mul_left]

/-! ### The radii, the geometric ratio `q`, and the strength and curvature -/

def PR : ℕ := 48
def qh : ℚ := expQ (-(27 / 500)) 14
def sigQ (i : ℕ) : ℚ := ((sigN.getD i 0 : ℤ) : ℚ) / 10 ^ 17
def rhat (i : ℕ) : ℚ := (ehat (sigQ i)) ^ 4
def aQ (i : ℕ) : ℕ := (qh * rhat i * 2 ^ PR).floor.toNat
def Sh : ℚ := ((⌊fS (qh ^ 2) * 2 ^ 60⌋ : ℤ) : ℚ) / 2 ^ 60
def Ch : ℚ := ((⌊fC (qh ^ 2) * 2 ^ 60⌋ : ℤ) : ℚ) / 2 ^ 60
def epsQ : ℚ := tayB (27 / 500) 14
def eps1 : ℚ := tayB (49 / 50) 20
def dSQ : ℚ := 54 * epsQ + 1 / 2 ^ 60
def dCQ : ℚ := 9 * epsQ + 1 / 2 ^ 60

def radChk (i : ℕ) : Bool :=
  decide (0 ≤ ehat (sigQ i)) && decide (ehat (sigQ i) ≤ 1) && decide (0 ≤ sigQ i) &&
  decide (sigQ i ≤ 4 * (49 / 50)) && decide (aQ i ≤ 2 ^ PR) && decide (0 ≤ qh * rhat i)

def gradChk : Bool :=
  decide (0 ≤ qh) && decide (qh ≤ 1) && decide (epsQ + 4 * eps1 ≤ 1 / 2 ^ PR)

theorem q_val : capSource.q = Real.exp (((-(27 / 500) : ℚ) : ℝ)) := by
  unfold CapSource.q
  show Real.exp (-(27 / 250 : ℝ) / 2) = _
  push_cast; norm_num

theorem q_pos : 0 < capSource.q := by unfold CapSource.q; exact Real.exp_pos _

theorem q_lt_one : capSource.q < 1 := by
  rw [q_val]
  have := Real.exp_lt_exp.mpr (show (((-(27 / 500) : ℚ) : ℝ)) < 0 by push_cast; norm_num)
  rwa [Real.exp_zero] at this

theorem q_err : |capSource.q - (qh : ℝ)| ≤ (epsQ : ℝ) := by
  rw [q_val]
  have h := exp_enc (-(27 / 500)) 14 (by norm_num) (by push_cast; rw [abs_neg]; norm_num)
  have e : |(-(27 / 500) : ℚ)| = 27 / 500 := by norm_num
  rw [e] at h
  exact h

theorem rad_val (i : ℕ) (hi : i < 16) :
    capSource.rad i = Real.exp (-((sigQ i : ℚ) : ℝ)) := by
  unfold CapSource.rad
  have : capSource.sigma i = (sigQ i : ℝ) := by
    show sigmaF i = _
    unfold sigmaF sigQ
    rw [show min i 15 = i by omega]
    push_cast; rfl
  rw [this]

theorem rad_data (i : ℕ) (hi : i < 16) (h : radChk i = true) (g : gradChk = true) :
    |(aQ i : ℝ) / 2 ^ PR - capSource.q * capSource.rad i| ≤ 2 / 2 ^ PR ∧
    0 ≤ (aQ i : ℝ) / 2 ^ PR ∧ (aQ i : ℝ) / 2 ^ PR ≤ 1 ∧ 0 ≤ capSource.q * capSource.rad i ∧
    capSource.q * capSource.rad i ≤ 1 := by
  unfold radChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  unfold gradChk at g
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  obtain ⟨⟨g1, g2⟩, g3⟩ := g
  have hP : (0 : ℝ) < 2 ^ PR := by positivity
  have hrad := rad_enc (sigQ i) h3 h4 h2 h1
  rw [← rad_val i hi] at hrad
  have hqe := q_err
  have hrad0 : 0 ≤ capSource.rad i := by rw [rad_val i hi]; exact (Real.exp_pos _).le
  have hrad1 : capSource.rad i ≤ 1 := by
    rw [rad_val i hi, Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ sigQ i := Rat.cast_nonneg.2 h3
    linarith
  have hq0 := q_pos
  have hq1 := q_lt_one
  have hqh0 : (0 : ℝ) ≤ qh := Rat.cast_nonneg.2 g1
  have hqh1 : (qh : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).2 g2; simpa using this
  have hgg : (epsQ : ℝ) + 4 * (eps1 : ℝ) ≤ 1 / 2 ^ PR := by
    have := (Rat.cast_le (K := ℝ)).2 g3
    push_cast at this; exact this
  have hrh : ((rhat i : ℚ) : ℝ) = ((ehat (sigQ i)) ^ 4 : ℚ) := rfl
  -- floor
  have hnn : (0 : ℚ) ≤ qh * rhat i * 2 ^ PR := by positivity
  have hfl1 : ((aQ i : ℕ) : ℝ) ≤ (qh : ℝ) * (rhat i : ℝ) * 2 ^ PR := by
    unfold aQ
    have h0 : 0 ≤ (qh * rhat i * 2 ^ PR).floor := Int.floor_nonneg.2 hnn
    have : (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℤ) = (qh * rhat i * 2 ^ PR).floor :=
      Int.toNat_of_nonneg h0
    have h3' : (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℚ) ≤ qh * rhat i * 2 ^ PR := by
      have h4' : (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℚ) = ((qh * rhat i * 2 ^ PR).floor : ℚ) := by
        exact_mod_cast this
      rw [h4']; exact Int.floor_le _
    have := (Rat.cast_le (K := ℝ)).2 h3'
    push_cast at this; exact this
  have hfl2 : (qh : ℝ) * (rhat i : ℝ) * 2 ^ PR < ((aQ i : ℕ) : ℝ) + 1 := by
    unfold aQ
    have h0 : 0 ≤ (qh * rhat i * 2 ^ PR).floor := Int.floor_nonneg.2 hnn
    have : (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℤ) = (qh * rhat i * 2 ^ PR).floor :=
      Int.toNat_of_nonneg h0
    have h3' : qh * rhat i * 2 ^ PR < (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℚ) + 1 := by
      have h4' : (((qh * rhat i * 2 ^ PR).floor.toNat : ℕ) : ℚ) = ((qh * rhat i * 2 ^ PR).floor : ℚ) := by
        exact_mod_cast this
      rw [h4']; exact Int.lt_floor_add_one _
    have := (Rat.cast_lt (K := ℝ)).2 h3'
    push_cast at this; exact this
  have hrhd : |capSource.rad i - (rhat i : ℝ)| ≤ 4 * (eps1 : ℝ) := by
    exact hrad
  have hepsQ0 : (0 : ℝ) ≤ (epsQ : ℝ) := Rat.cast_nonneg.2 (by unfold epsQ tayB; positivity)
  have hprod : |capSource.q * capSource.rad i - (qh : ℝ) * (rhat i : ℝ)| ≤ (epsQ : ℝ) + 4 * (eps1 : ℝ) := by
    have e : capSource.q * capSource.rad i - (qh : ℝ) * (rhat i : ℝ) =
        (capSource.q - qh) * capSource.rad i + (qh : ℝ) * (capSource.rad i - (rhat i : ℝ)) := by ring
    rw [e]
    calc _ ≤ |(capSource.q - qh) * capSource.rad i| + |(qh : ℝ) * (capSource.rad i - (rhat i : ℝ))| :=
          abs_add_le _ _
      _ = |capSource.q - qh| * capSource.rad i + (qh : ℝ) * |capSource.rad i - (rhat i : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hrad0, abs_of_nonneg hqh0]
      _ ≤ (epsQ : ℝ) * 1 + 1 * (4 * (eps1 : ℝ)) := by
          apply add_le_add
          · exact mul_le_mul hqe hrad1 hrad0 hepsQ0
          · exact mul_le_mul hqh1 hrhd (abs_nonneg _) zero_le_one
      _ = _ := by ring
  have hx : |(aQ i : ℝ) / 2 ^ PR - (qh : ℝ) * (rhat i : ℝ)| ≤ 1 / 2 ^ PR := by
    have e1 : (aQ i : ℝ) / 2 ^ PR ≤ (qh : ℝ) * (rhat i : ℝ) := by
      rw [div_le_iff₀ hP]; exact hfl1
    have e2 : (qh : ℝ) * (rhat i : ℝ) < (aQ i : ℝ) / 2 ^ PR + 1 / 2 ^ PR := by
      rw [← add_div, lt_div_iff₀ hP]; exact hfl2
    rw [abs_le]; constructor <;> linarith
  refine ⟨?_, by positivity, ?_, mul_nonneg hq0.le hrad0, ?_⟩
  · have := abs_sub_le ((aQ i : ℝ) / 2 ^ PR) ((qh : ℝ) * (rhat i : ℝ)) (capSource.q * capSource.rad i)
    have e3 : |(qh : ℝ) * (rhat i : ℝ) - capSource.q * capSource.rad i| ≤ 1 / 2 ^ PR := by
      rw [abs_sub_comm]; exact hprod.trans hgg
    calc _ ≤ 1 / 2 ^ PR + 1 / 2 ^ PR := this.trans (add_le_add hx e3)
      _ = 2 / 2 ^ PR := by ring
  · rw [div_le_one hP]; exact_mod_cast h5
  · calc capSource.q * capSource.rad i ≤ 1 * 1 := mul_le_mul hq1.le hrad1 hrad0 zero_le_one
      _ = 1 := one_mul 1

/-! ### Strength and curvature -/

theorem S_val : capSource.strength =
    3 * (1 - (capSource.q ^ 2) ^ 2) / (2 * (1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2)) ∧
    capSource.curvature =
    (1 - capSource.q ^ 2) ^ 2 / (2 * (1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2)) := by
  have hq0 := q_pos
  have hq1 := q_lt_one
  set r : ℝ := capSource.q ^ 2 with hr
  have h0 : 0 < r := by positivity
  have hr1 : r < 1 := by nlinarith
  have hr1' : 0 < 1 - r := by linarith
  have hA : 0 < 1 + 4 * r + r ^ 2 := by positivity
  have hN : capSource.normalizer = (1 + 4 * r + r ^ 2) / (1 - r) ^ 2 := by
    unfold CapSource.normalizer; rw [← hr]
  constructor
  · unfold CapSource.strength
    rw [hN, ← hr]
    field_simp
    ring
  · unfold CapSource.curvature
    rw [hN]
    field_simp

theorem floor_div_err (x : ℚ) (n : ℕ) :
    0 ≤ x - ((⌊x * 2 ^ n⌋ : ℤ) : ℚ) / 2 ^ n ∧ x - ((⌊x * 2 ^ n⌋ : ℤ) : ℚ) / 2 ^ n < 1 / 2 ^ n := by
  have hn : (0 : ℚ) < 2 ^ n := by positivity
  have h1 := Int.floor_le (x * 2 ^ n)
  have h2 := Int.lt_floor_add_one (x * 2 ^ n)
  constructor
  · rw [sub_nonneg, div_le_iff₀ hn]; exact h1
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hn]; linarith

theorem S_err (g : gradChk = true) : |capSource.strength - (Sh : ℝ)| ≤ (dSQ : ℝ) ∧
    |capSource.curvature - (Ch : ℝ)| ≤ (dCQ : ℝ) := by
  unfold gradChk at g
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  obtain ⟨⟨g1, g2⟩, g3⟩ := g
  obtain ⟨hS, hC⟩ := S_val
  have hq0 := q_pos
  have hq1 := q_lt_one
  have hqe := q_err
  have hqh0 : (0 : ℝ) ≤ qh := Rat.cast_nonneg.2 g1
  have hqh1 : (qh : ℝ) ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).2 g2; simpa using this
  have hr0 : 0 ≤ capSource.q ^ 2 := by positivity
  have hr1 : capSource.q ^ 2 ≤ 1 := by nlinarith
  have hr0' : 0 ≤ (qh : ℝ) ^ 2 := by positivity
  have hr1' : (qh : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hepsQ0 : (0 : ℝ) ≤ (epsQ : ℝ) := Rat.cast_nonneg.2 (by unfold epsQ tayB; positivity)
  have hdr : |capSource.q ^ 2 - (qh : ℝ) ^ 2| ≤ 2 * (epsQ : ℝ) := by
    have e : capSource.q ^ 2 - (qh : ℝ) ^ 2 = (capSource.q - qh) * (capSource.q + qh) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ capSource.q + (qh : ℝ))]
    calc _ ≤ (epsQ : ℝ) * 2 := mul_le_mul hqe (by linarith) (by linarith) hepsQ0
      _ = _ := by ring
  have f1 := floor_div_err (fS (qh ^ 2)) 60
  have f2 := floor_div_err (fC (qh ^ 2)) 60
  have f1R : 0 ≤ (fS (qh ^ 2) : ℝ) - (Sh : ℝ) ∧ (fS (qh ^ 2) : ℝ) - (Sh : ℝ) < 1 / 2 ^ 60 := by
    have a := (Rat.cast_le (K := ℝ)).2 f1.1
    have b := (Rat.cast_lt (K := ℝ)).2 f1.2
    unfold Sh
    push_cast at a b ⊢
    exact ⟨a, b⟩
  have f2R : 0 ≤ (fC (qh ^ 2) : ℝ) - (Ch : ℝ) ∧ (fC (qh ^ 2) : ℝ) - (Ch : ℝ) < 1 / 2 ^ 60 := by
    have a := (Rat.cast_le (K := ℝ)).2 f2.1
    have b := (Rat.cast_lt (K := ℝ)).2 f2.2
    unfold Ch
    push_cast at a b ⊢
    exact ⟨a, b⟩
  have hs1 := fS_lip hr0 hr1 hr0' hr1'
  have hc1 := fC_lip hr0 hr1 hr0' hr1'
  have eS : (fS (qh ^ 2) : ℝ) = 3 * (1 - ((qh : ℝ) ^ 2) ^ 2) / (2 * (1 + 4 * (qh : ℝ) ^ 2 + ((qh : ℝ) ^ 2) ^ 2)) := by
    unfold fS; push_cast; ring
  have eC : (fC (qh ^ 2) : ℝ) = (1 - (qh : ℝ) ^ 2) ^ 2 / (2 * (1 + 4 * (qh : ℝ) ^ 2 + ((qh : ℝ) ^ 2) ^ 2)) := by
    unfold fC; push_cast; ring
  have hdS : (dSQ : ℝ) = 54 * (epsQ : ℝ) + 1 / 2 ^ 60 := by unfold dSQ; push_cast; ring
  have hdC : (dCQ : ℝ) = 9 * (epsQ : ℝ) + 1 / 2 ^ 60 := by unfold dCQ; push_cast; ring
  constructor
  · rw [hS, hdS]
    rw [← eS] at hs1
    have := abs_sub_le (3 * (1 - (capSource.q ^ 2) ^ 2) / (2 * (1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2)))
      (fS (qh ^ 2) : ℝ) (Sh : ℝ)
    have h3 : |(fS (qh ^ 2) : ℝ) - (Sh : ℝ)| ≤ 1 / 2 ^ 60 := by
      rw [abs_of_nonneg f1R.1]; exact f1R.2.le
    have h4 : 18 * |capSource.q ^ 2 - (qh : ℝ) ^ 2| ≤ 36 * (epsQ : ℝ) := by linarith
    linarith
  · rw [hC, hdC]
    rw [← eC] at hc1
    have := abs_sub_le ((1 - capSource.q ^ 2) ^ 2 / (2 * (1 + 4 * capSource.q ^ 2 + (capSource.q ^ 2) ^ 2)))
      (fC (qh ^ 2) : ℝ) (Ch : ℝ)
    have h3 : |(fC (qh ^ 2) : ℝ) - (Ch : ℝ)| ≤ 1 / 2 ^ 60 := by
      rw [abs_of_nonneg f2R.1]; exact f2R.2.le
    have h4 : 3 * |capSource.q ^ 2 - (qh : ℝ) ^ 2| ≤ 6 * (epsQ : ℝ) := by linarith
    linarith


/-! ### The packed weight matrix and the row sums -/

def BW : ℕ := 2 ^ 96
def idxA (e : ℕ × ℕ × ℕ) : ℕ := e.1 + 16 * e.2.1
def PkW : ℕ := (paN.map fun e => e.2.2 * BW ^ idxA e).sum
def Wm (j i : ℕ) : ℕ := PkW / BW ^ (i + 16 * j) % BW
def Wpack (j : ℕ) : ℕ := ((List.range 16).map fun i => Wm j i * BW ^ i).sum
def WpL : List ℕ := (List.range 94).map Wpack
def Wtot (i : ℕ) : ℕ := ((List.range 94).map fun j => Wm j i).sum

def rowS (k : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, w :: ws => uTab ((k * j) % 186) * w + rowS k (j + 1) ws

def Sk (k : ℕ) : ℕ := rowS k 0 WpL

def Tk (k : ℕ) : ℤ := ((List.range 16).map fun i =>
  ((aQ i ^ k : ℕ) : ℤ) * (((Sk k / BW ^ i % BW : ℕ) : ℤ) - 2 ^ (FB + 1) * (Wtot i : ℤ))).sum

/-- weights that survive the packing -/
def aCnt (m : ℕ) : ℕ := (paN.map fun e => if idxA e = m then e.2.2 else 0).sum

theorem paN_mem {e : ℕ × ℕ × ℕ} (h : e ∈ paN) : ∃ t ∈ paT, e = (t.1.toNat, t.2.1.toNat, t.2.2.toNat) := by
  unfold paN at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ⟨t, ht, rfl⟩

theorem paN_range {e : ℕ × ℕ × ℕ} (h : e ∈ paN) : e.1 < 16 ∧ e.2.1 ≤ 93 := by
  obtain ⟨t, ht, rfl⟩ := paN_mem h
  obtain ⟨h0, h1, h2⟩ := paT_range t ht
  have := (pa_ok t ht).2
  constructor <;> simp <;> omega

theorem idxA_lt {e : ℕ × ℕ × ℕ} (h : e ∈ paN) : idxA e < 1504 := by
  obtain ⟨h1, h2⟩ := paN_range h
  unfold idxA; omega

theorem idxA_mod {e : ℕ × ℕ × ℕ} (h : e ∈ paN) : idxA e % 16 = e.1 ∧ idxA e / 16 = e.2.1 := by
  obtain ⟨h1, h2⟩ := paN_range h
  unfold idxA; constructor <;> omega

theorem paN_sum : (paN.map fun e => e.2.2).sum = MM := by
  have key : ∀ L : List Tr, (∀ t ∈ L, 0 ≤ t.2.2) →
      (((L.map fun t => t.2.2.toNat).sum : ℕ) : ℤ) = sumP L := by
    intro L
    induction L with
    | nil => intro _; simp [sumP]
    | cons t L ih =>
      intro h
      have h1 := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      have h2 : 0 ≤ t.2.2 := h t (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, h1, sumP]
      rw [Int.toNat_of_nonneg h2]
  have := key paT (fun t ht => (pa_ok t ht).1)
  unfold MM
  have e : (paN.map fun e => e.2.2) = paT.map fun t => t.2.2.toNat := by
    unfold paN; rw [List.map_map]; rfl
  rw [e]
  have h0 : (0 : ℤ) ≤ sumP paT := pa_tot.le
  omega

theorem aCnt_le (m : ℕ) : aCnt m ≤ MM := by
  rw [← paN_sum]
  unfold aCnt
  apply List.sum_le_sum
  intro e _
  split_ifs <;> simp

theorem Wm_eq (hM : MM < BW) (m : ℕ) (hm : m < 1504) : PkW / BW ^ m % BW = aCnt m := by
  have hB : 0 < BW := by unfold BW; positivity
  have h1 : PkW = ∑ m ∈ Finset.range 1504, aCnt m * BW ^ m := by
    unfold PkW aCnt
    exact regroup paN idxA 1504 (fun e he => idxA_lt he) (fun e => e.2.2) (fun m => BW ^ m)
  rw [h1]
  exact digit_sum BW hB 1504 aCnt (fun m _ => lt_of_le_of_lt (aCnt_le m) hM) m hm

theorem Wm_eq' (hM : MM < BW) (j i : ℕ) (hj : j < 94) (hi : i < 16) : Wm j i = aCnt (i + 16 * j) := by
  unfold Wm
  exact Wm_eq hM _ (by omega)

theorem rowS_eq (k : ℕ) : ∀ (ws : List ℕ) (j : ℕ), rowS k j ws =
    ∑ idx ∈ Finset.range ws.length, uTab ((k * (j + idx)) % 186) * ws.getD idx 0 := by
  intro ws
  induction ws with
  | nil => intro j; simp [rowS]
  | cons w ws ih =>
    intro j
    rw [rowS, ih (j + 1), List.length_cons, Finset.sum_range_succ']
    have hs : ∑ idx ∈ Finset.range ws.length, uTab ((k * (j + 1 + idx)) % 186) * ws.getD idx 0 =
        ∑ idx ∈ Finset.range ws.length, uTab ((k * (j + (idx + 1))) % 186) * (w :: ws).getD (idx + 1) 0 :=
      Finset.sum_congr rfl (fun idx _ => by rw [show j + 1 + idx = j + (idx + 1) by ring]; rfl)
    rw [hs]
    simp only [List.getD_cons_zero, add_zero]
    ring

theorem WpL_getD (idx : ℕ) (h : idx < 94) : WpL.getD idx 0 = Wpack idx := by
  unfold WpL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some]

theorem WpL_length : WpL.length = 94 := by simp [WpL]

theorem Sk_eq (k : ℕ) : Sk k = ∑ j ∈ Finset.range 94, uTab ((k * j) % 186) * Wpack j := by
  unfold Sk
  rw [rowS_eq, WpL_length]
  apply Finset.sum_congr rfl; intro j hj
  rw [WpL_getD j (Finset.mem_range.1 hj), zero_add]


/-! ### Digits of the row sums and the packed identity -/

theorem list_range_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem uTab_le (m : ℕ) (hm : m < 186) : uTab m < 2 ^ (FB + 2) := by
  rw [uTab_eq m hm]; exact (u_spec m (by omega)).1

theorem Sk_digit (hWt : ∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) (k i : ℕ) (hi : i < 16) :
    Sk k / BW ^ i % BW = ∑ j ∈ Finset.range 94, uTab ((k * j) % 186) * Wm j i := by
  have hB : 0 < BW := by unfold BW; positivity
  have h1 : Sk k = ∑ i ∈ Finset.range 16, (∑ j ∈ Finset.range 94, uTab ((k * j) % 186) * Wm j i) * BW ^ i := by
    rw [Sk_eq]
    simp only [Wpack, list_range_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [h1]
  refine digit_sum BW hB 16 (fun i => ∑ j ∈ Finset.range 94, uTab ((k * j) % 186) * Wm j i) ?_ i hi
  intro i hi
  calc (∑ j ∈ Finset.range 94, uTab ((k * j) % 186) * Wm j i)
      ≤ ∑ j ∈ Finset.range 94, 2 ^ (FB + 2) * Wm j i := by
        apply Finset.sum_le_sum; intro j _
        exact Nat.mul_le_mul_right _ (uTab_le _ (Nat.mod_lt _ (by norm_num))).le
    _ = 2 ^ (FB + 2) * Wtot i := by
        rw [← Finset.mul_sum]; unfold Wtot; rw [list_range_sum]
    _ < BW := hWt i hi

noncomputable def cosA (k j : ℕ) : ℝ := ((uTab ((k * j) % 186) : ℝ) - 2 ^ (FB + 1)) / 2 ^ FB

theorem Tk_cast (hWt : ∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) (k : ℕ) (hM : MM < BW) :
    (Tk k : ℝ) = ∑ i ∈ Finset.range 16, (aQ i : ℝ) ^ k *
      ∑ j ∈ Finset.range 94, ((uTab ((k * j) % 186) : ℝ) - 2 ^ (FB + 1)) * (Wm j i : ℝ) := by
  unfold Tk
  rw [list_range_sum, Int.cast_sum]
  apply Finset.sum_congr rfl; intro i hi
  have hd := Sk_digit hWt k i (Finset.mem_range.1 hi)
  have hd' : ((Sk k / BW ^ i % BW : ℕ) : ℝ) =
      ∑ j ∈ Finset.range 94, (uTab ((k * j) % 186) : ℝ) * (Wm j i : ℝ) := by
    rw [hd]; push_cast; rfl
  have hw : (Wtot i : ℝ) = ∑ j ∈ Finset.range 94, (Wm j i : ℝ) := by
    unfold Wtot; rw [list_range_sum]; push_cast; rfl
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow]
  rw [hd', hw, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  ring

theorem Zhat_eq (hWt : ∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) (hM : MM < BW) (k : ℕ) :
    (paN.map fun e => (e.2.2 : ℝ) * ((aQ e.1 : ℝ) / 2 ^ PR) ^ k * cosA k e.2.1).sum =
      (Tk k : ℝ) / 2 ^ (PR * k + FB) := by
  -- regroup by the packing index
  set F : ℕ → ℝ := fun m => ((aQ (m % 16) : ℝ) / 2 ^ PR) ^ k * cosA k (m / 16) with hF
  have h1 : (paN.map fun e => (e.2.2 : ℝ) * ((aQ e.1 : ℝ) / 2 ^ PR) ^ k * cosA k e.2.1) =
      paN.map (fun e => (e.2.2 : ℝ) * F (idxA e)) := by
    apply List.map_congr_left; intro e he
    obtain ⟨hm, hd⟩ := idxA_mod he
    simp only [hF, hm, hd]; ring
  rw [h1, regroup paN idxA 1504 (fun e he => idxA_lt he) (fun e => (e.2.2 : ℝ)) F]
  have h2 : ∀ m, (paN.map fun e => if idxA e = m then (e.2.2 : ℝ) else 0).sum = (aCnt m : ℝ) := by
    intro m
    unfold aCnt
    rw [Nat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left; intro e _
    simp only [Function.comp]
    split_ifs <;> simp
  simp only [h2]
  -- split the index
  have h3 : ∀ J : ℕ, ∑ m ∈ Finset.range (16 * J), (aCnt m : ℝ) * F m =
      ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range 16, (aCnt (i + 16 * j) : ℝ) * F (i + 16 * j) := by
    intro J
    induction J with
    | zero => simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty]
    | succ J ih =>
      have e1 : 16 * (J + 1) = 16 * J + 16 := by ring
      rw [e1, Finset.sum_range_add, ih, Finset.sum_range_succ
        (fun j => ∑ i ∈ Finset.range 16, (aCnt (i + 16 * j) : ℝ) * F (i + 16 * j)) J]
      have e3 : ∑ x ∈ Finset.range 16, (aCnt (16 * J + x) : ℝ) * F (16 * J + x) =
          ∑ i ∈ Finset.range 16, (aCnt (i + 16 * J) : ℝ) * F (i + 16 * J) :=
        Finset.sum_congr rfl (fun i _ => by rw [add_comm (16 * J) i])
      rw [e3]
  rw [show (1504 : ℕ) = 16 * 94 by norm_num, h3 94, Tk_cast hWt k hM, Finset.sum_div, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  have hi' := Finset.mem_range.1 hi
  rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [← Wm_eq' hM j i (Finset.mem_range.1 hj) hi'])]
  apply Finset.sum_congr rfl; intro j hj
  have hmod : (i + 16 * j) % 16 = i := by omega
  have hdiv : (i + 16 * j) / 16 = j := by omega
  simp only [hF, hmod, hdiv, cosA]
  have e2 : (2 : ℝ) ^ (PR * k + FB) = (2 ^ PR) ^ k * 2 ^ FB := by rw [pow_add, pow_mul]
  rw [e2, div_pow]
  ring


/-! ### The radial coefficient against its enclosure -/

def tauQ : ℚ := ((sumP row0 - sumP gasPosT : ℤ) : ℚ) / (sumP row0 : ℚ)
def gam : ℚ := 1 / 2 ^ FB + 8 / 10 ^ 13
def cKh (k : ℕ) : ℚ := (1 + Sh * k + Ch * (k : ℚ) ^ 2) / k
def RhatQ (k : ℕ) : ℚ := -(cKh k) * tauQ * (Tk k : ℚ) / ((MM : ℚ) * 2 ^ (PR * k + FB))
def ErrQ (k : ℕ) : ℚ :=
  tauQ * ((dSQ + k * dCQ) + |cKh k| * (k * (2 / 2 ^ PR) + gam))

theorem tgt_pos_eq : tgt Sign.pos = (tauQ : ℝ) := by
  have hT : (sumP row0 : ℝ) ≠ 0 := tot_ne
  unfold tgt tauQ
  rw [massPos]
  push_cast
  field_simp

theorem cos_link (k j : ℕ) :
    |cosA k j - Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / 93))| ≤ (gam : ℝ) := by
  have hm : (k * j) % 186 < 186 := Nat.mod_lt _ (by norm_num)
  have hu := (u_spec ((k * j) % 186) (by omega)).2
  have e1 : cosA k j = ((uOf ((k * j) % 186) (gpow ((k * j) % 186)).1 : ℕ) - (2 : ℝ) ^ (FB + 1)) / 2 ^ FB := by
    unfold cosA; rw [uTab_eq _ hm]
  have e2 : Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / 93)) = Real.cos (((k * j) % 186 : ℕ) * Real.pi / 93) := by
    have hkj : k * j = (k * j) % 186 + 186 * ((k * j) / 186) := (Nat.mod_add_div _ _).symm
    have : (k : ℝ) * (Real.pi * (j : ℝ) / 93) = (((k * j) % 186 : ℕ) * Real.pi / 93) + (((k * j) / 186 : ℕ) : ℝ) * (2 * Real.pi) := by
      have h2 : ((k * j : ℕ) : ℝ) = (((k * j) % 186 : ℕ) : ℝ) + 186 * (((k * j) / 186 : ℕ) : ℝ) := by
        exact_mod_cast hkj
      push_cast at h2
      rw [mul_div_assoc', show (k : ℝ) * (Real.pi * j) = (k * j) * Real.pi by ring, h2]
      ring
    rw [this, Real.cos_add_nat_mul_two_pi]
  rw [e1, e2]
  have : (gam : ℝ) = 1 / 2 ^ FB + 8 / 10 ^ 13 := by unfold gam; push_cast; ring
  rw [this]
  exact hu

theorem entry_err (hrad : ∀ i < 16, radChk i = true) (hg : gradChk = true) (k : ℕ)
    {e : ℕ × ℕ × ℕ} (he : e ∈ paN) :
    |zTerm k e - (e.2.2 : ℝ) * ((aQ e.1 : ℝ) / 2 ^ PR) ^ k * cosA k e.2.1| ≤
      (e.2.2 : ℝ) * (k * (2 / 2 ^ PR) + (gam : ℝ)) := by
  obtain ⟨hi, hj⟩ := paN_range he
  obtain ⟨d1, d2, d3, d4, d5⟩ := rad_data e.1 hi (hrad e.1 hi) hg
  have hp : (0 : ℝ) ≤ (e.2.2 : ℝ) := Nat.cast_nonneg _
  set x : ℝ := (aQ e.1 : ℝ) / 2 ^ PR with hx
  set ν : ℝ := capSource.q * capSource.rad e.1 with hν
  set c : ℝ := Real.cos ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93)) with hc
  have hpow := CatalanMeasure.GenD.Signed.RouteI.MomentInputs.abs_pow_sub_pow_le_unit d4 d5 d2 d3 k
  have hpow' : |ν ^ k - x ^ k| ≤ k * (2 / 2 ^ PR) := by
    refine hpow.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [abs_sub_comm]; exact d1
  have hcl := cos_link k e.2.1
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one _
  have hx0 : 0 ≤ x ^ k := pow_nonneg d2 k
  have hx1 : x ^ k ≤ 1 := pow_le_one₀ d2 d3
  have key : |ν ^ k * c - x ^ k * cosA k e.2.1| ≤ k * (2 / 2 ^ PR) + (gam : ℝ) := by
    have e1 : ν ^ k * c - x ^ k * cosA k e.2.1 = (ν ^ k - x ^ k) * c + x ^ k * (c - cosA k e.2.1) := by ring
    rw [e1]
    calc _ ≤ |(ν ^ k - x ^ k) * c| + |x ^ k * (c - cosA k e.2.1)| := abs_add_le _ _
      _ = |ν ^ k - x ^ k| * |c| + x ^ k * |c - cosA k e.2.1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx0]
      _ ≤ (k * (2 / 2 ^ PR)) * 1 + 1 * (gam : ℝ) := by
          apply add_le_add
          · exact mul_le_mul hpow' hc1 (abs_nonneg _) (by positivity)
          · apply mul_le_mul hx1 _ (abs_nonneg _) zero_le_one
            rw [abs_sub_comm]; exact hcl
      _ = _ := by ring
  have e2 : zTerm k e - (e.2.2 : ℝ) * x ^ k * cosA k e.2.1 = (e.2.2 : ℝ) * (ν ^ k * c - x ^ k * cosA k e.2.1) := by
    unfold zTerm; rw [← hν, ← hc]; ring
  rw [e2, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left key hp


theorem dSQ_nn : (0 : ℝ) ≤ (dSQ : ℝ) := Rat.cast_nonneg.2 (by unfold dSQ epsQ tayB; positivity)
theorem dCQ_nn : (0 : ℝ) ≤ (dCQ : ℝ) := Rat.cast_nonneg.2 (by unfold dCQ epsQ tayB; positivity)

theorem MM_pos : (0 : ℝ) < MM := by
  rw [MM_real]; exact_mod_cast pa_tot

theorem paN_sum_real : ((paN.map fun e => (e.2.2 : ℝ))).sum = (MM : ℝ) := by
  have := paN_sum
  have h : (((paN.map fun e => e.2.2).sum : ℕ) : ℝ) = MM := by rw [this]
  rw [Nat.cast_list_sum, List.map_map] at h
  exact h

theorem Z_err (hWt : ∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) (hM : MM < BW)
    (hrad : ∀ i < 16, radChk i = true) (hg : gradChk = true) (k : ℕ) :
    |Ztrue k - (Tk k : ℝ) / 2 ^ (PR * k + FB)| ≤ (MM : ℝ) * (k * (2 / 2 ^ PR) + (gam : ℝ)) := by
  have h := MomentSource.list_abs_sum_le paN (zTerm k)
    (fun e => (e.2.2 : ℝ) * ((aQ e.1 : ℝ) / 2 ^ PR) ^ k * cosA k e.2.1)
    (fun e => (e.2.2 : ℝ) * (k * (2 / 2 ^ PR) + (gam : ℝ))) (fun e he => entry_err hrad hg k he)
  rw [Zhat_eq hWt hM k] at h
  rw [List.sum_map_mul_right, paN_sum_real] at h
  exact h

theorem Z_bd (hrad : ∀ i < 16, radChk i = true) (hg : gradChk = true) (k : ℕ) :
    |Ztrue k| ≤ (MM : ℝ) := by
  have h := MomentSource.list_abs_sum_le paN (zTerm k) (fun _ => 0) (fun e => (e.2.2 : ℝ)) (by
    intro e he
    obtain ⟨hi, hj⟩ := paN_range he
    obtain ⟨d1, d2, d3, d4, d5⟩ := rad_data e.1 hi (hrad e.1 hi) hg
    unfold zTerm
    rw [sub_zero, abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg d4]
    have := Real.abs_cos_le_one ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93))
    have h2 : (capSource.q * capSource.rad e.1) ^ k ≤ 1 := pow_le_one₀ d4 d5
    have hp : (0 : ℝ) ≤ (e.2.2 : ℝ) := Nat.cast_nonneg _
    have h3 : (capSource.q * capSource.rad e.1) ^ k * |Real.cos ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93))| ≤ 1 :=
      mul_le_one₀ h2 (abs_nonneg _) this
    nlinarith [mul_le_mul_of_nonneg_left h3 hp])
  have e0 : (paN.map fun _ => (0 : ℝ)).sum = 0 := by simp [List.map_const']
  rw [e0, sub_zero, paN_sum_real] at h
  exact h

theorem rad_err (hWt : ∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) (hM : MM < BW)
    (hrad : ∀ i < 16, radChk i = true) (hg : gradChk = true) (k : ℕ) (hk : 1 ≤ k) :
    |radCoef capSource k - (RhatQ k : ℝ)| ≤ (ErrQ k : ℝ) := by
  have hz1 := Z_err hWt hM hrad hg k
  have hz2 := Z_bd hrad hg k
  obtain ⟨hs, hc⟩ := S_err hg
  have hMp := MM_pos
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hgn : 0 ≤ (tauQ : ℝ) := by rw [← tgt_pos_eq]; exact tgt_nonneg _
  rw [radCoef_form k, tgt_pos_eq]
  set Zh : ℝ := (Tk k : ℝ) / 2 ^ (PR * k + FB) with hZh
  -- constants
  have hcK : |cK k - (cKh k : ℝ)| ≤ (dSQ : ℝ) + k * (dCQ : ℝ) := by
    have e : cK k - (cKh k : ℝ) = (capSource.strength - (Sh : ℝ)) + (capSource.curvature - (Ch : ℝ)) * k := by
      unfold cK cKh; push_cast; field_simp; ring
    rw [e]
    calc _ ≤ |capSource.strength - (Sh : ℝ)| + |(capSource.curvature - (Ch : ℝ)) * k| := abs_add_le _ _
      _ = |capSource.strength - (Sh : ℝ)| + |capSource.curvature - (Ch : ℝ)| * k := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
      _ ≤ (dSQ : ℝ) + (dCQ : ℝ) * k := add_le_add hs (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
      _ = _ := by ring
  have hRh : (RhatQ k : ℝ) = -((tauQ : ℝ) / MM) * (cKh k : ℝ) * Zh := by
    unfold RhatQ; rw [hZh]; push_cast
    field_simp
  have hpr : -((tauQ : ℝ) / MM) * cK k * Ztrue k - (RhatQ k : ℝ) =
      -((tauQ : ℝ) / MM) * ((cK k * Ztrue k) - (cKh k : ℝ) * Zh) := by rw [hRh]; ring
  rw [hpr, abs_mul, abs_neg, abs_div, abs_of_nonneg hgn, abs_of_pos hMp]
  have hmain : |cK k * Ztrue k - (cKh k : ℝ) * Zh| ≤
      ((dSQ : ℝ) + k * (dCQ : ℝ)) * MM + |(cKh k : ℝ)| * ((MM : ℝ) * (k * (2 / 2 ^ PR) + (gam : ℝ))) := by
    have e : cK k * Ztrue k - (cKh k : ℝ) * Zh = (cK k - (cKh k : ℝ)) * Ztrue k + (cKh k : ℝ) * (Ztrue k - Zh) := by ring
    rw [e]
    calc _ ≤ |(cK k - (cKh k : ℝ)) * Ztrue k| + |(cKh k : ℝ) * (Ztrue k - Zh)| := abs_add_le _ _
      _ = |cK k - (cKh k : ℝ)| * |Ztrue k| + |(cKh k : ℝ)| * |Ztrue k - Zh| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul hcK hz2 (abs_nonneg _) (add_nonneg dSQ_nn (mul_nonneg (Nat.cast_nonneg k) dCQ_nn)))
          (mul_le_mul_of_nonneg_left hz1 (abs_nonneg _))
  have hEr : (ErrQ k : ℝ) = (tauQ : ℝ) * (((dSQ : ℝ) + k * (dCQ : ℝ)) + |(cKh k : ℝ)| * (k * (2 / 2 ^ PR) + (gam : ℝ))) := by
    unfold ErrQ; push_cast; ring
  rw [hEr]
  have hMM : (tauQ : ℝ) / MM * (((dSQ : ℝ) + k * (dCQ : ℝ)) * MM + |(cKh k : ℝ)| * ((MM : ℝ) * (k * (2 / 2 ^ PR) + (gam : ℝ)))) =
      (tauQ : ℝ) * (((dSQ : ℝ) + k * (dCQ : ℝ)) + |(cKh k : ℝ)| * (k * (2 / 2 ^ PR) + (gam : ℝ))) := by
    field_simp
  rw [← hMM]
  exact mul_le_mul_of_nonneg_left hmain (div_nonneg hgn hMp.le)


/-! ### The tail majorant -/

def KR : ℕ := 68

def WR (i : ℕ) : ℕ := (paN.map fun e => if e.1 = i then e.2.2 else 0).sum

/-- the weighted powers of the upper radii, rounded up on a `2^-60` grid -/
def mj (k : ℕ) : ℕ :=
  ((∑ i ∈ Finset.range 16, WR i * (aQ i + 2) ^ k) * 2 ^ 60 + (2 ^ (PR * k) - 1)) / 2 ^ (PR * k)

def BdMaj (k : ℕ) : ℚ :=
  tauQ * (|cKh k| + dSQ + k * dCQ) * ((mj k : ℚ) / 2 ^ 60) / MM

def Bd (k : ℕ) : ℚ := if k ≤ KR then |RhatQ k| + ErrQ k else BdMaj k

theorem WR_sum (G : ℕ → ℝ) :
    (paN.map fun e => (e.2.2 : ℝ) * G e.1).sum = ∑ i ∈ Finset.range 16, (WR i : ℝ) * G i := by
  have h := regroup paN (fun e => e.1) 16 (fun e he => (paN_range he).1) (fun e => (e.2.2 : ℝ)) G
  rw [h]
  apply Finset.sum_congr rfl; intro i _
  have hW : ((WR i : ℕ) : ℝ) = (paN.map fun t => if t.1 = i then (t.2.2 : ℝ) else 0).sum := by
    unfold WR
    rw [Nat.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun e _ => ?_))
    simp only [Function.comp]
    split_ifs <;> simp
  rw [hW]

theorem mj_ge (k : ℕ) :
    ∑ i ∈ Finset.range 16, (WR i : ℝ) * (((aQ i : ℝ) + 2) / 2 ^ PR) ^ k ≤ (mj k : ℝ) / 2 ^ 60 := by
  have hD : 1 ≤ 2 ^ (PR * k) := Nat.one_le_two_pow
  set N : ℕ := ∑ i ∈ Finset.range 16, WR i * (aQ i + 2) ^ k with hN
  have e1 : ∑ i ∈ Finset.range 16, (WR i : ℝ) * (((aQ i : ℝ) + 2) / 2 ^ PR) ^ k = (N : ℝ) / 2 ^ (PR * k) := by
    rw [hN]; push_cast; rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [div_pow, pow_mul]; ring
  rw [e1]
  have hq := Nat.div_add_mod (N * 2 ^ 60 + (2 ^ (PR * k) - 1)) (2 ^ (PR * k))
  have hr := Nat.mod_lt (N * 2 ^ 60 + (2 ^ (PR * k) - 1)) (show 0 < 2 ^ (PR * k) by omega)
  have hle : N * 2 ^ 60 ≤ 2 ^ (PR * k) * mj k := by
    unfold mj
    generalize N * 2 ^ 60 = A at *
    generalize 2 ^ (PR * k) = D at *
    generalize (A + (D - 1)) / D = c at *
    generalize (A + (D - 1)) % D = r at *
    generalize D * c = X at *
    omega
  have hleR : (N : ℝ) * 2 ^ 60 ≤ 2 ^ (PR * k) * (mj k : ℝ) := by exact_mod_cast hle
  have hP : (0 : ℝ) < 2 ^ (PR * k) := by positivity
  rw [div_le_div_iff₀ hP (by positivity)]
  linarith

theorem maj_err (hrad : ∀ i < 16, radChk i = true) (hg : gradChk = true) (k : ℕ) (hk : 1 ≤ k) :
    |radCoef capSource k| ≤ (BdMaj k : ℝ) := by
  obtain ⟨hs, hc⟩ := S_err hg
  have hMp := MM_pos
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgn : 0 ≤ (tauQ : ℝ) := by rw [← tgt_pos_eq]; exact tgt_nonneg _
  rw [radCoef_form k, tgt_pos_eq]
  -- bound on |Z|
  have hZ : |Ztrue k| ≤ ∑ i ∈ Finset.range 16, (WR i : ℝ) * (((aQ i : ℝ) + 2) / 2 ^ PR) ^ k := by
    rw [← WR_sum]
    have h := MomentSource.list_abs_sum_le paN (zTerm k) (fun _ => 0)
      (fun e => (e.2.2 : ℝ) * (((aQ e.1 : ℝ) + 2) / 2 ^ PR) ^ k) (by
      intro e he
      obtain ⟨hi, hj⟩ := paN_range he
      obtain ⟨d1, d2, d3, d4, d5⟩ := rad_data e.1 hi (hrad e.1 hi) hg
      have hP : (0 : ℝ) < 2 ^ PR := by positivity
      have hν : capSource.q * capSource.rad e.1 ≤ ((aQ e.1 : ℝ) + 2) / 2 ^ PR := by
        have := (abs_le.1 d1).1
        have e2 : ((aQ e.1 : ℝ) + 2) / 2 ^ PR = (aQ e.1 : ℝ) / 2 ^ PR + 2 / 2 ^ PR := by ring
        rw [e2]; linarith
      unfold zTerm
      rw [sub_zero, abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg d4]
      have h2 : (capSource.q * capSource.rad e.1) ^ k ≤ (((aQ e.1 : ℝ) + 2) / 2 ^ PR) ^ k :=
        pow_le_pow_left₀ d4 hν k
      have hc1 := Real.abs_cos_le_one ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93))
      have hp : (0 : ℝ) ≤ (e.2.2 : ℝ) := Nat.cast_nonneg _
      have h3 : (capSource.q * capSource.rad e.1) ^ k * |Real.cos ((k : ℝ) * (Real.pi * (e.2.1 : ℝ) / 93))| ≤
          (((aQ e.1 : ℝ) + 2) / 2 ^ PR) ^ k := by
        calc _ ≤ (capSource.q * capSource.rad e.1) ^ k * 1 :=
              mul_le_mul_of_nonneg_left hc1 (pow_nonneg d4 k)
          _ ≤ _ := by rw [mul_one]; exact h2
      nlinarith [mul_le_mul_of_nonneg_left h3 hp])
    have e0 : (paN.map fun _ => (0 : ℝ)).sum = 0 := by simp [List.map_const']
    rw [e0, sub_zero] at h
    exact h
  have hcK : |cK k| ≤ |(cKh k : ℝ)| + ((dSQ : ℝ) + k * (dCQ : ℝ)) := by
    have e : cK k - (cKh k : ℝ) = (capSource.strength - (Sh : ℝ)) + (capSource.curvature - (Ch : ℝ)) * k := by
      unfold cK cKh; push_cast; field_simp; ring
    have h1 : |cK k - (cKh k : ℝ)| ≤ (dSQ : ℝ) + k * (dCQ : ℝ) := by
      rw [e]
      calc _ ≤ |capSource.strength - (Sh : ℝ)| + |(capSource.curvature - (Ch : ℝ)) * k| := abs_add_le _ _
        _ = |capSource.strength - (Sh : ℝ)| + |capSource.curvature - (Ch : ℝ)| * k := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k)]
        _ ≤ (dSQ : ℝ) + (dCQ : ℝ) * k := add_le_add hs (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
        _ = _ := by ring
    have := abs_sub_abs_le_abs_sub (cK k) (cKh k : ℝ)
    linarith
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_nonneg hgn, abs_of_pos hMp]
  have hBd : (BdMaj k : ℝ) = (tauQ : ℝ) * (|(cKh k : ℝ)| + (dSQ : ℝ) + k * (dCQ : ℝ)) *
      ((mj k : ℝ) / 2 ^ 60) / MM := by
    unfold BdMaj
    push_cast
    ring
  rw [hBd]
  have hZ' : |Ztrue k| ≤ (mj k : ℝ) / 2 ^ 60 := hZ.trans (mj_ge k)
  have hcc : |cK k| ≤ |(cKh k : ℝ)| + (dSQ : ℝ) + k * (dCQ : ℝ) := by linarith
  calc (tauQ : ℝ) / MM * |cK k| * |Ztrue k|
      ≤ (tauQ : ℝ) / MM * (|(cKh k : ℝ)| + (dSQ : ℝ) + k * (dCQ : ℝ)) *
        ((mj k : ℝ) / 2 ^ 60) := by
        apply mul_le_mul _ hZ' (abs_nonneg _) (by
          apply mul_nonneg (div_nonneg hgn hMp.le)
          exact le_trans (abs_nonneg _) hcc)
        exact mul_le_mul_of_nonneg_left hcc (div_nonneg hgn hMp.le)
    _ = _ := by ring


/-! ### Kernel checks and assembly -/

def radCheck (k : ℕ) : Bool := decide (|RhatQ k - alL.getD k 0| + ErrQ k ≤ 1 / 10000)

def hypsChk : Bool :=
  decide (MM < BW) && (List.range 16).all (fun i => decide (2 ^ (FB + 2) * Wtot i < BW)) &&
    (List.range 16).all radChk && gradChk

def radKernel : Bool := (List.range 32).all fun i => radCheck (i + 1)

def tailSum : ℚ := ∑ i ∈ Finset.range 352, Bd (33 + i)

def tailKernel : Bool := decide (tailSum ≤ 1 / 200)

def radialKernel : Bool := hypsChk && radKernel && tailKernel

set_option maxRecDepth 100000 in
theorem radialKernel_true : radialKernel = true := by
  -- kcost: 7.5 s measured 6 Nov (68 row sums of 94 table digits against one packed weight matrix; 316 tail powers)
  decide +kernel

theorem hypsChk_true : hypsChk = true := by
  have h := radialKernel_true
  unfold radialKernel at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem radKernel_true : radKernel = true := by
  have h := radialKernel_true
  unfold radialKernel at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem tailKernel_true : tailKernel = true := by
  have h := radialKernel_true
  unfold radialKernel at h
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem hyps_unpack : MM < BW ∧ (∀ i < 16, 2 ^ (FB + 2) * Wtot i < BW) ∧
    (∀ i < 16, radChk i = true) ∧ gradChk = true := by
  have h := hypsChk_true
  unfold hypsChk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem radial_all (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 32) :
    |radCoef capSource k - (alL.getD k 0 : ℚ)| ≤ 1 / 10000 := by
  obtain ⟨hM, hWt, hrad, hg⟩ := hyps_unpack
  have h := rad_err hWt hM hrad hg k hk1
  have hK := radKernel_true
  unfold radKernel at hK
  simp only [List.all_eq_true, List.mem_range] at hK
  have hc := hK (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hc
  unfold radCheck at hc
  simp only [decide_eq_true_eq] at hc
  have hc' : (|RhatQ k - alL.getD k 0| : ℝ) + (ErrQ k : ℝ) ≤ 1 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).2 hc
    push_cast at this ⊢
    exact this
  have e2 : |((RhatQ k : ℝ) - ((alL.getD k 0 : ℚ) : ℝ))| = (|RhatQ k - alL.getD k 0| : ℝ) := by
    push_cast; rfl
  have t := abs_add_le (radCoef capSource k - (RhatQ k : ℝ)) ((RhatQ k : ℝ) - ((alL.getD k 0 : ℚ) : ℝ))
  have e : radCoef capSource k - ((alL.getD k 0 : ℚ) : ℝ) =
      (radCoef capSource k - (RhatQ k : ℝ)) + ((RhatQ k : ℝ) - ((alL.getD k 0 : ℚ) : ℝ)) := by ring
  rw [e]
  linarith

theorem tail_all : ∑ i ∈ Finset.range 352, |radCoef capSource (32 + i + 1)| ≤ 1 / 200 := by
  obtain ⟨hM, hWt, hrad, hg⟩ := hyps_unpack
  have hper : ∀ i ∈ Finset.range 352, |radCoef capSource (32 + i + 1)| ≤ (Bd (33 + i) : ℝ) := by
    intro i _
    have hk : 32 + i + 1 = 33 + i := by ring
    rw [hk]
    unfold Bd
    split_ifs with hle
    · have h := rad_err hWt hM hrad hg (33 + i) (by omega)
      push_cast
      have := abs_sub_abs_le_abs_sub (radCoef capSource (33 + i)) (RhatQ (33 + i) : ℝ)
      linarith [abs_nonneg (radCoef capSource (33 + i) - (RhatQ (33 + i) : ℝ))]
    · exact maj_err hrad hg (33 + i) (by omega)
  have hT := tailKernel_true
  unfold tailKernel at hT
  simp only [decide_eq_true_eq] at hT
  have hT' : (tailSum : ℝ) ≤ 1 / 200 := by
    have := (Rat.cast_le (K := ℝ)).2 hT
    push_cast at this ⊢
    exact this
  calc _ ≤ ∑ i ∈ Finset.range 352, (Bd (33 + i) : ℝ) := Finset.sum_le_sum hper
    _ = (tailSum : ℝ) := by unfold tailSum; push_cast; rfl
    _ ≤ 1 / 200 := hT'

theorem nearDataClosed_capSource : NearDataClosed capSource where
  moment := near_moment
  radial := radial_all
  tail := tail_all

theorem nearHf_capSource : CatalanMeasure.GenD.Signed.RouteI.CompactInstance.NearHf capSource (Trunc.finite 384) :=
  CompactHf.nearHf_closed capSource capSource_admissible (by show 31 ≤ 899; norm_num)
    rfl nearDataClosed_capSource
    capSource_eps_ge capSource_eps_le capSource_massL_pos_ge



end CatalanMeasure.GenD.Signed.RouteI.NearDataCert

#print axioms CatalanMeasure.GenD.Signed.RouteI.NearDataCert.nearDataClosed_capSource
#print axioms CatalanMeasure.GenD.Signed.RouteI.NearDataCert.nearHf_capSource
