module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.CompactHf
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance

@[expose] public section

set_option Elab.async false

/-!
# Route I `AnchorE2`: the E2 anchor-moment enclosure (t4b, 7 Nov 2026)

Theory of the enclosure of `L = 2 <rowT R, da> + <anchorV R C, dv>` for the anchor-0 cells of
`CapSourceData` (the `hL0`, `hL1` of `T4Instance.hI_of_moves`).  Part 1 (this block) is the cell
calculus: for a positive row cell `[lo,hi]` (`2 <= lo`) and an integer polynomial `z`,
`int_FZ`: `int_lo^hi z(vY Y) dY = F(vY hi) - F(vY lo)` with the primitive `FZ` built from
`Gp j = int t^j (1 - t^-2)` (`momK` of `CompactHf`), `FZ_deriv`, the mean value bound `FZ_lip`,
brackets of `vY` by rationals, and the logarithm of a rational near 1.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.AnchorE2

open Set MeasureTheory intervalIntegral Filter
open CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.T4Instance
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one vY_add_inv vY_continuous)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (momK integral_vY_pow')
open CatalanMeasure.GenD.Signed.RouteI.CapFields (YCell)

noncomputable section

/-! ### Primitives -/

/-- A primitive of `t^j (1 - t^-2)`. -/
def Gp (j : ℕ) (t : ℝ) : ℝ := if j = 0 then t + t⁻¹ else -momK j t

/-- The primitive of `z(t) (1 - t^-2)` for `z = sum a_i t^i`, indices starting at `j`. -/
def FZ : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: q, j, t => (a : ℝ) * Gp j t + FZ q (j + 1) t

theorem continuous_evalZ' (q : List ℤ) : Continuous (evalZ q) := by
  induction q with
  | nil => simp [evalZ]; exact continuous_const
  | cons a q ih =>
    have : evalZ (a :: q) = fun x => (a : ℝ) + x * evalZ q x := by funext x; simp [evalZ]
    rw [this]; fun_prop

theorem int_Gp (j : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ Y in a..b, vY Y ^ j = Gp j (vY b) - Gp j (vY a) := by
  by_cases hj : j = 0
  · subst hj
    have e : ∫ Y in a..b, vY Y ^ 0 = b - a := by simp
    rw [e]
    simp only [Gp, if_true]
    rw [vY_add_inv (by linarith), vY_add_inv ha]
  · have := integral_vY_pow' (Nat.one_le_iff_ne_zero.mpr hj) ha hab
    simp only [Gp, hj, ite_false]
    rw [this]; ring

theorem int_FZ (q : List ℤ) : ∀ (j : ℕ) {a b : ℝ}, 2 ≤ a → a ≤ b →
    ∫ Y in a..b, vY Y ^ j * evalZ q (vY Y) = FZ q j (vY b) - FZ q j (vY a) := by
  induction q with
  | nil => intro j a b ha hab; simp [evalZ, FZ]
  | cons c q ih =>
    intro j a b ha hab
    have hfun : (fun Y => vY Y ^ j * evalZ (c :: q) (vY Y)) =
        fun Y => (c : ℝ) * vY Y ^ j + vY Y ^ (j + 1) * evalZ q (vY Y) := by
      funext Y; simp only [evalZ]; ring
    rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, int_Gp j ha hab, ih (j + 1) ha hab]
    · simp only [FZ]; ring
    · exact ((continuous_const.mul (vY_continuous.pow j))).intervalIntegrable _ _
    · exact ((vY_continuous.pow (j + 1)).mul ((continuous_evalZ' q).comp vY_continuous)).intervalIntegrable _ _

/-! ### Derivative and Lipschitz bound -/

theorem Gp_deriv (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Gp j) (t ^ j * (1 - (t⁻¹) ^ 2)) t := by
  have ht0 : t ≠ 0 := ht.ne'
  by_cases h0 : j = 0
  · subst h0
    have h := (hasDerivAt_id t).add (hasDerivAt_inv ht0)
    have e : Gp 0 = fun t => id t + t⁻¹ := by funext s; simp [Gp]
    rw [e]
    convert h using 1
    field_simp; ring
  · by_cases h1 : j = 1
    · subst h1
      have e : Gp 1 = fun t => t ^ 2 / 2 - Real.log t := by
        funext s; simp [Gp, momK, MomentSource.H1] <;> ring
      rw [e]
      have h := ((hasDerivAt_pow 2 t).div_const 2).sub (Real.hasDerivAt_log ht0)
      convert h using 1
      field_simp; ring
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have e : Gp (m + 2) = fun t => t ^ (m + 3) / ((m : ℝ) + 3) - t ^ (m + 1) / ((m : ℝ) + 1) := by
        funext s
        simp only [Gp, momK, show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ite_false]
        have : m + 2 - 1 = m + 1 := by omega
        rw [this]; push_cast; ring
      rw [e]
      have h := ((hasDerivAt_pow (m + 3) t).div_const ((m : ℝ) + 3)).sub
        ((hasDerivAt_pow (m + 1) t).div_const ((m : ℝ) + 1))
      convert h using 1
      have h3 : ((m : ℝ) + 3) ≠ 0 := by positivity
      have h1' : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem FZ_deriv (q : List ℤ) : ∀ (j : ℕ) {t : ℝ}, 0 < t →
    HasDerivAt (FZ q j) (t ^ j * evalZ q t * (1 - (t⁻¹) ^ 2)) t := by
  induction q with
  | nil =>
    intro j t ht
    have : FZ [] j = fun _ => (0 : ℝ) := by funext s; simp [FZ]
    rw [this]; simpa [evalZ] using hasDerivAt_const t (0 : ℝ)
  | cons a q ih =>
    intro j t ht
    have e : FZ (a :: q) j = fun s => (a : ℝ) * Gp j s + FZ q (j + 1) s := by funext s; simp [FZ]
    rw [e]
    have h := ((Gp_deriv j ht).const_mul (a : ℝ)).add (ih (j + 1) ht)
    convert h using 1
    simp only [evalZ]; ring

/-- Mean value bound: on `[a, b] ⊂ (0, 1]`, if `|z| <= B` on `[0,1]`, then
`|F(b) - F(a)| <= B/a^2 (b - a)` for `F = FZ z 0 + c log` with `|c| <= C`: the derivative of
`F` is bounded by `B/a^2 + C/a`. -/
theorem FZ_lip (q : List ℤ) {B c : ℝ} (hB : ∀ x ∈ Icc (0 : ℝ) 1, |evalZ q x| ≤ B) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(FZ q 0 b + c * Real.log b) - (FZ q 0 a + c * Real.log a)| ≤
      (B / a ^ 2 + |c| / a) * (b - a) := by
  have hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt (fun t => FZ q 0 t + c * Real.log t)
      (x ^ 0 * evalZ q x * (1 - (x⁻¹) ^ 2) + c * x⁻¹) (Icc a b) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    exact ((FZ_deriv q 0 hx0).add ((Real.hasDerivAt_log hx0.ne').const_mul c)).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc a b,
      ‖x ^ 0 * evalZ q x * (1 - (x⁻¹) ^ 2) + c * x⁻¹‖ ≤ B / a ^ 2 + |c| / a := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hx1 : x ≤ 1 := hx.2.trans hb
    have h1 : |evalZ q x| ≤ B := hB x ⟨hx0.le, hx1⟩
    have hinv : (a⁻¹) ^ 2 ≥ (x⁻¹) ^ 2 := by
      have : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hx.1
      exact pow_le_pow_left₀ (inv_nonneg.mpr hx0.le) this 2
    have hxi1 : 1 ≤ (x⁻¹) ^ 2 := by
      have : 1 ≤ x⁻¹ := one_le_inv_iff₀.mpr ⟨hx0, hx1⟩
      nlinarith
    have h2 : |1 - (x⁻¹) ^ 2| ≤ (a⁻¹) ^ 2 := by
      rw [abs_of_nonpos (by linarith)]; nlinarith [sq_nonneg (x⁻¹)]
    have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
    have h3 : |c * x⁻¹| ≤ |c| / a := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hx0), ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (abs_nonneg _) ha hx.1
    rw [Real.norm_eq_abs]
    calc |x ^ 0 * evalZ q x * (1 - (x⁻¹) ^ 2) + c * x⁻¹|
        ≤ |x ^ 0 * evalZ q x * (1 - (x⁻¹) ^ 2)| + |c * x⁻¹| := abs_add_le _ _
      _ ≤ B * (a⁻¹) ^ 2 + |c| / a := by
          gcongr
          rw [abs_mul, pow_zero, one_mul]
          exact mul_le_mul h1 h2 (abs_nonneg _) hB0
      _ = B / a ^ 2 + |c| / a := by rw [inv_pow]; ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc a b)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  simpa using this

/-! ### Brackets of `vY` by rationals -/

theorem le_vY_of {s Y : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hY : 2 ≤ Y) (h : Y ≤ s + s⁻¹) :
    s ≤ vY Y := by
  by_contra hlt
  push Not at hlt
  have hv := vY_pos hY
  have hsum := vY_add_inv hY
  have key : vY Y + (vY Y)⁻¹ > s + s⁻¹ := by
    have : vY Y + (vY Y)⁻¹ - (s + s⁻¹) = (s - vY Y) * (1 / (vY Y * s) - 1) := by
      field_simp; ring
    have h1 : 0 < s - vY Y := by linarith
    have h2 : 1 < 1 / (vY Y * s) := by
      rw [lt_div_iff₀ (mul_pos hv hs)]; nlinarith
    have : 0 < (s - vY Y) * (1 / (vY Y * s) - 1) := mul_pos h1 (by linarith)
    linarith
  linarith

theorem vY_le_of {s Y : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hY : 2 ≤ Y) (h : s + s⁻¹ ≤ Y) :
    vY Y ≤ s := by
  by_contra hlt
  push Not at hlt
  have hv := vY_pos hY
  have hv1 := vY_le_one hY
  have hsum := vY_add_inv hY
  have : vY Y + (vY Y)⁻¹ < s + s⁻¹ := by
    have e : s + s⁻¹ - (vY Y + (vY Y)⁻¹) = (vY Y - s) * (1 / (vY Y * s) - 1) := by
      field_simp; ring
    have h1 : 0 < vY Y - s := by linarith
    have h2 : 1 < 1 / (vY Y * s) := by
      rw [lt_div_iff₀ (mul_pos hv hs)]; nlinarith
    have : 0 < (vY Y - s) * (1 / (vY Y * s) - 1) := mul_pos h1 (by linarith)
    linarith
  linarith

/-! ### Logarithm of a rational near 1 -/

/-- Partial sum of `-log ρ = sum x^(i+1)/(i+1)`, `x = 1 - ρ`. -/
def logSeries (ρ : ℚ) (N : ℕ) : ℚ := -∑ i ∈ Finset.range N, (1 - ρ) ^ (i + 1) / ((i : ℚ) + 1)

/-- The remainder bound. -/
def logRem (ρ : ℚ) (N : ℕ) : ℚ := |1 - ρ| ^ (N + 1) / (1 - |1 - ρ|)

theorem log_enc {ρ : ℚ} (N : ℕ) (h : |1 - ρ| < 1) :
    |Real.log (ρ : ℝ) - (logSeries ρ N : ℝ)| ≤ (logRem ρ N : ℝ) := by
  have hx : |((1 - ρ : ℚ) : ℝ)| < 1 := by exact_mod_cast h
  have := Real.abs_log_sub_add_sum_range_le hx N
  have e : (1 : ℝ) - ((1 - ρ : ℚ) : ℝ) = (ρ : ℝ) := by push_cast; ring
  rw [e] at this
  have e2 : Real.log (ρ : ℝ) - (logSeries ρ N : ℝ) =
      (∑ i ∈ Finset.range N, ((1 - ρ : ℚ) : ℝ) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (ρ : ℝ) := by
    unfold logSeries; push_cast; ring
  rw [e2]
  convert this using 2
  unfold logRem; push_cast; rfl

/-! ### Explicit rational form of the primitive -/

def gn (m : ℕ) (t : ℝ) : ℝ :=
  if m = 0 then t + t⁻¹ else if m = 1 then t ^ 2 / 2
  else t ^ (m + 1) / ((m : ℝ) + 1) - t ^ (m - 1) / ((m : ℝ) - 1)

theorem Gp_log (m : ℕ) (t : ℝ) : Gp m t + (if m = 1 then Real.log t else 0) = gn m t := by
  by_cases h0 : m = 0
  · subst h0; simp [Gp, gn]
  by_cases h1 : m = 1
  · subst h1; simp [Gp, gn, momK, MomentSource.H1] <;> ring
  simp only [Gp, gn, momK, h0, h1, ite_false, add_zero]; ring

def FSum : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: q, j, t => (a : ℝ) * gn j t + FSum q (j + 1) t

/-- The coefficient of `log t` in `FSum - FZ`. -/
def lc : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: q, j => (if j = 1 then a else 0) + lc q (j + 1)

theorem FZ_log (q : List ℤ) : ∀ (j : ℕ) (t : ℝ),
    FZ q j t + (lc q j : ℝ) * Real.log t = FSum q j t := by
  induction q with
  | nil => intro j t; simp [FZ, lc, FSum]
  | cons a q ih =>
    intro j t
    have h := ih (j + 1) t
    have g := Gp_log j t
    simp only [FZ, lc, FSum, Int.cast_add]
    rw [← h, ← g]
    by_cases hj : j = 1
    · simp only [hj, ite_true]; push_cast; ring
    · simp only [hj, ite_false]; push_cast; ring

theorem lc_ge2 (q : List ℤ) : ∀ j, 2 ≤ j → lc q j = 0 := by
  induction q with
  | nil => intro j _; simp [lc]
  | cons a q ih => intro j hj; simp only [lc]; rw [if_neg (by omega), ih (j + 1) (by omega)]; simp

theorem lc_zero (a b : ℤ) (r : List ℤ) : lc (a :: b :: r) 0 = b := by
  simp [lc, lc_ge2 r 2 le_rfl]

theorem FSum_zero (a b : ℤ) (r : List ℤ) (t : ℝ) :
    FSum (a :: b :: r) 0 t = a * (t + t⁻¹) + b * (t ^ 2 / 2) + FSum r 2 t := by
  simp [FSum, gn]; ring

/-- Entry `k` is `l_k * (K / (s + k))`. -/
def wJ (K : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | s, a :: q => (a * (K / (s : ℤ))) :: wJ K (s + 1) q

theorem FSum_ge2 (K : ℤ) : ∀ (q : List ℤ) (i : ℕ),
    (∀ m : ℕ, 1 ≤ m → m ≤ i + q.length + 2 → (m : ℤ) ∣ K) → ∀ t : ℝ,
    (K : ℝ) * FSum q (i + 2) t =
      t ^ (i + 3) * evalZ (wJ K (i + 3) q) t - t ^ (i + 1) * evalZ (wJ K (i + 1) q) t := by
  intro q
  induction q with
  | nil => intro i _ t; simp [FSum, wJ, evalZ]
  | cons a q ih =>
    intro i hd t
    have h3 : ((i + 3 : ℕ) : ℤ) ∣ K := hd (i + 3) (by omega) (by simp only [List.length_cons]; omega)
    have h1 : ((i + 1 : ℕ) : ℤ) ∣ K := hd (i + 1) (by omega) (by simp only [List.length_cons]; omega)
    have ih' := ih (i + 1) (fun m hm1 hm2 => hd m hm1 (by simp only [List.length_cons]; omega)) t
    have c3 : (((K / ((i + 3 : ℕ) : ℤ) : ℤ)) : ℝ) = (K : ℝ) / ((i : ℝ) + 3) := by
      have := Int.cast_div (α := ℝ) h3 (by positivity)
      push_cast at this ⊢; exact this
    have c1 : (((K / ((i + 1 : ℕ) : ℤ) : ℤ)) : ℝ) = (K : ℝ) / ((i : ℝ) + 1) := by
      have := Int.cast_div (α := ℝ) h1 (by positivity)
      push_cast at this ⊢; exact this
    simp only [FSum, wJ, evalZ, gn, show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega, ite_false]
    rw [show i + 1 + 3 = i + 4 from rfl, show i + 1 + 1 = i + 2 from rfl] at ih'
    simp only [Nat.cast_add, Nat.cast_ofNat] at *
    have e1 : i + 2 + 1 = i + 3 := rfl
    have e2 : i + 2 - 1 = i + 1 := rfl
    rw [e1, e2]
    push_cast at c3 c1 ⊢
    rw [mul_add, ih', c3, c1]
    have hi3 : ((i : ℝ) + 3) ≠ 0 := by positivity
    have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hi2 : ((i : ℝ) + 2 + 1) = (i : ℝ) + 3 := by ring
    have hi2' : ((i : ℝ) + 2 - 1) = (i : ℝ) + 1 := by ring
    rw [hi2, hi2']
    field_simp
    ring

/-- The integer polynomial `t * K * FSum` (for `z = a :: b :: r`): `K FSum z 0 t = t⁻¹ W(t)`. -/
def Wpoly (K a b : ℤ) (r : List ℤ) : List ℤ :=
  addL [a * K, 0, a * K, b * (K / 2)]
    (addL (0 :: 0 :: 0 :: 0 :: wJ K 3 r) (smulL (-1) (0 :: 0 :: wJ K 1 r)))

theorem FSum_W (K a b : ℤ) (r : List ℤ) (hd : ∀ m : ℕ, 1 ≤ m → m ≤ r.length + 2 → (m : ℤ) ∣ K)
    (t : ℝ) (ht : t ≠ 0) :
    (K : ℝ) * FSum (a :: b :: r) 0 t = t⁻¹ * evalZ (Wpoly K a b r) t := by
  have h2 : (2 : ℤ) ∣ K := by simpa using hd 2 (by norm_num) (by omega)
  have c2 : ((K / 2 : ℤ) : ℝ) = (K : ℝ) / 2 := by
    have := Int.cast_div (α := ℝ) h2 (by norm_num)
    push_cast at this; exact this
  have hF := FSum_ge2 K r 0 (fun m hm1 hm2 => hd m hm1 (by omega)) t
  unfold Wpoly
  simp only [evalZ_addL, evalZ_smulL, evalZ]
  rw [FSum_zero]
  simp only [zero_add, Nat.zero_add, pow_one] at hF
  have key : (K : ℝ) * FSum r 2 t = t ^ 3 * evalZ (wJ K 3 r) t - t * evalZ (wJ K 1 r) t := by
    simpa using hF
  have e : (K : ℝ) * ((a : ℝ) * (t + t⁻¹) + (b : ℝ) * (t ^ 2 / 2) + FSum r 2 t) =
      K * (a * (t + t⁻¹)) + K * (b * (t ^ 2 / 2)) + K * FSum r 2 t := by ring
  rw [e, key]
  push_cast
  rw [c2]
  field_simp
  ring

/-- Integer Horner at the point `n / S`: `S^len * z (n / S)`. -/
def hornS : List ℤ → ℤ → ℕ → ℤ
  | [], _, _ => 0
  | a :: q, n, S => a * (S : ℤ) ^ (q.length + 1) + n * hornS q n S

theorem hornS_eq (z : List ℤ) (n : ℤ) {S : ℕ} (hS : 0 < S) :
    (hornS z n S : ℝ) = (S : ℝ) ^ z.length * evalZ z ((n : ℝ) / S) := by
  induction z with
  | nil => simp [hornS, evalZ]
  | cons a q ih =>
    simp only [hornS, evalZ, List.length_cons]
    push_cast
    rw [ih]
    have : (S : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### The cell bound (positive cells) -/

/-- `FSum z 0 (n / 2^k)` as an exact rational, from the integer Horner value of `W = Wpoly`. -/
def FSq (W : List ℤ) (K : ℤ) (n : ℕ) (k : ℕ) : ℚ :=
  (hornS W n (2 ^ k) : ℚ) * 2 ^ k / ((K : ℚ) * n * (((2 ^ k : ℕ) : ℚ)) ^ W.length)

theorem FSq_eq {K a b : ℤ} {r : List ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ r.length + 2 → (m : ℤ) ∣ K) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ((FSq (Wpoly K a b r) K n k : ℚ) : ℝ) = FSum (a :: b :: r) 0 ((n : ℝ) / 2 ^ k) := by
  have hS : 0 < 2 ^ k := by positivity
  have ht : (n : ℝ) / 2 ^ k ≠ 0 := by positivity
  have h1 := FSum_W K a b r hd ((n : ℝ) / 2 ^ k) ht
  have h2 := hornS_eq (Wpoly K a b r) n hS
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hSr : (((2 ^ k : ℕ)) : ℝ) = 2 ^ k := by push_cast; ring
  unfold FSq
  push_cast
  have e : FSum (a :: b :: r) 0 ((n : ℝ) / 2 ^ k) =
      ((n : ℝ) / 2 ^ k)⁻¹ * evalZ (Wpoly K a b r) ((n : ℝ) / 2 ^ k) / K := by
    field_simp at h1 ⊢; linarith
  rw [e]
  have h3 : evalZ (Wpoly K a b r) ((n : ℝ) / 2 ^ k) =
      (hornS (Wpoly K a b r) n (2 ^ k) : ℝ) / (2 ^ k) ^ (Wpoly K a b r).length := by
    push_cast at h2
    rw [h2]; field_simp
  rw [h3]
  field_simp

def hiLogQ (ρ : ℚ) (N : ℕ) : ℚ := logSeries ρ N + logRem ρ N
def loLogQ (ρ : ℚ) (N : ℕ) : ℚ := logSeries ρ N - logRem ρ N

/-- The upper bound of the cell integral from the dyadic data `n1, n2` (numerators over `2^k`). -/
def cellUB (W : List ℤ) (K a1 : ℤ) (B : ℚ) (k N n1 n2 : ℕ) : ℚ :=
  FSq W K n2 k - FSq W K n1 k + (B * 2 ^ k / (n2 : ℚ) ^ 2 + |(a1 : ℚ)| / n2) +
    (B * 2 ^ k / (n1 : ℚ) ^ 2 + |(a1 : ℚ)| / n1) +
    max ((a1 : ℚ) * hiLogQ (((n1 : ℚ) + 1) / n2) N) ((a1 : ℚ) * loLogQ ((n1 : ℚ) / ((n2 : ℚ) + 1)) N)

theorem cell_ub {K a0 a1 : ℤ} {r : List ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ r.length + 2 → (m : ℤ) ∣ K) {B : ℚ}
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, |evalZ (a0 :: a1 :: r) x| ≤ (B : ℝ)) {lo hi : ℝ}
    (hlo : 2 ≤ lo) (hlh : lo ≤ hi) {k N n1 n2 : ℕ} (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hn1' : n1 + 1 ≤ 2 ^ k) (hn2' : n2 + 1 ≤ 2 ^ k)
    (h1l : (n1 : ℝ) / 2 ^ k ≤ vY lo) (h1u : vY lo ≤ ((n1 : ℝ) + 1) / 2 ^ k)
    (h2l : (n2 : ℝ) / 2 ^ k ≤ vY hi) (h2u : vY hi ≤ ((n2 : ℝ) + 1) / 2 ^ k)
    (hρp : |1 - ((n1 : ℚ) + 1) / n2| < 1) (hρm : |1 - (n1 : ℚ) / ((n2 : ℚ) + 1)| < 1) :
    ∫ Y in lo..hi, evalZ (a0 :: a1 :: r) (vY Y) ≤
      (cellUB (Wpoly K a0 a1 r) K a1 B k N n1 n2 : ℝ) := by
  set z := a0 :: a1 :: r with hz
  have hhi : 2 ≤ hi := hlo.trans hlh
  have hS : (0 : ℝ) < 2 ^ k := by positivity
  have hv1 := vY_pos hlo
  have hv2 := vY_pos hhi
  have hv1' := vY_le_one hlo
  have hv2' := vY_le_one hhi
  -- the integral
  have hI : ∫ Y in lo..hi, evalZ z (vY Y) = FZ z 0 (vY hi) - FZ z 0 (vY lo) := by
    have := int_FZ z 0 hlo hlh
    simpa using this
  have hlc : (lc z 0 : ℝ) = a1 := by rw [hz, lc_zero]
  have hF : ∀ t, FZ z 0 t = FSum z 0 t - a1 * Real.log t := by
    intro t
    have := FZ_log z 0 t
    rw [hlc] at this; linarith
  -- dyadic points
  have ha1 : (0 : ℝ) < (n1 : ℝ) / 2 ^ k := by positivity
  have ha2 : (0 : ℝ) < (n2 : ℝ) / 2 ^ k := by positivity
  have e1 := FZ_lip z (c := a1) hB ha1 h1l hv1'
  have e2 := FZ_lip z (c := a1) hB ha2 h2l hv2'
  have g1 : ∀ t, FZ z 0 t + (a1 : ℝ) * Real.log t = FSum z 0 t := by
    intro t; have := FZ_log z 0 t; rw [hlc] at this; exact this
  rw [g1, g1] at e1 e2
  rw [abs_le] at e1 e2
  -- error terms
  have hn1r : (0 : ℝ) < n1 := by exact_mod_cast hn1
  have hn2r : (0 : ℝ) < n2 := by exact_mod_cast hn2
  have E1 : (B / ((n1 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n1 : ℝ) / 2 ^ k)) * (vY lo - (n1 : ℝ) / 2 ^ k) ≤
      (B : ℝ) * 2 ^ k / (n1 : ℝ) ^ 2 + |(a1 : ℝ)| / n1 := by
    have hpos : 0 ≤ B / ((n1 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n1 : ℝ) / 2 ^ k) := by
      have : (0 : ℝ) ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
      positivity
    calc _ ≤ (B / ((n1 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n1 : ℝ) / 2 ^ k)) * (1 / 2 ^ k) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          have : ((n1 : ℝ) + 1) / 2 ^ k = (n1 : ℝ) / 2 ^ k + 1 / 2 ^ k := by ring
          linarith
      _ = _ := by field_simp
  have E2 : (B / ((n2 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n2 : ℝ) / 2 ^ k)) * (vY hi - (n2 : ℝ) / 2 ^ k) ≤
      (B : ℝ) * 2 ^ k / (n2 : ℝ) ^ 2 + |(a1 : ℝ)| / n2 := by
    have hpos : 0 ≤ B / ((n2 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n2 : ℝ) / 2 ^ k) := by
      have : (0 : ℝ) ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
      positivity
    calc _ ≤ (B / ((n2 : ℝ) / 2 ^ k) ^ 2 + |(a1 : ℝ)| / ((n2 : ℝ) / 2 ^ k)) * (1 / 2 ^ k) := by
          apply mul_le_mul_of_nonneg_left _ hpos
          have : ((n2 : ℝ) + 1) / 2 ^ k = (n2 : ℝ) / 2 ^ k + 1 / 2 ^ k := by ring
          linarith
      _ = _ := by field_simp
  -- logarithm
  have hρ1 : ((n1 : ℝ)) / ((n2 : ℝ) + 1) ≤ vY lo / vY hi := by
    rw [div_le_div_iff₀ (by positivity) hv2]
    have a : (n1 : ℝ) ≤ vY lo * 2 ^ k := (div_le_iff₀ hS).mp h1l
    have b : vY hi * 2 ^ k ≤ (n2 : ℝ) + 1 := (le_div_iff₀ hS).mp h2u
    have h : (n1 * vY hi) * 2 ^ k ≤ (vY lo * ((n2 : ℝ) + 1)) * 2 ^ k := by
      nlinarith [mul_le_mul_of_nonneg_left b hn1r.le, mul_le_mul_of_nonneg_right a (by positivity : (0 : ℝ) ≤ (n2 : ℝ) + 1)]
    exact le_of_mul_le_mul_right h hS
  have hρ2 : vY lo / vY hi ≤ ((n1 : ℝ) + 1) / n2 := by
    rw [div_le_div_iff₀ hv2 hn2r]
    have a : (n2 : ℝ) ≤ vY hi * 2 ^ k := (div_le_iff₀ hS).mp h2l
    have b : vY lo * 2 ^ k ≤ (n1 : ℝ) + 1 := (le_div_iff₀ hS).mp h1u
    nlinarith [mul_le_mul_of_nonneg_left a hv1.le, mul_le_mul_of_nonneg_right b hv2.le]
  have hlogp := log_enc N hρp
  have hlogm := log_enc N hρm
  have hcp : (((((n1 : ℚ) + 1) / n2 : ℚ)) : ℝ) = ((n1 : ℝ) + 1) / n2 := by push_cast; ring
  have hcm : ((((n1 : ℚ) / ((n2 : ℚ) + 1) : ℚ)) : ℝ) = (n1 : ℝ) / ((n2 : ℝ) + 1) := by push_cast; ring
  rw [hcp] at hlogp
  rw [hcm] at hlogm
  have hpos_m : (0 : ℝ) < (n1 : ℝ) / ((n2 : ℝ) + 1) := by positivity
  have hL1 : Real.log ((n1 : ℝ) / ((n2 : ℝ) + 1)) ≤ Real.log (vY lo / vY hi) :=
    Real.log_le_log hpos_m hρ1
  have hL2 : Real.log (vY lo / vY hi) ≤ Real.log (((n1 : ℝ) + 1) / n2) :=
    Real.log_le_log (div_pos hv1 hv2) hρ2
  have hhi : Real.log (vY lo / vY hi) ≤ (hiLogQ (((n1 : ℚ) + 1) / n2) N : ℝ) := by
    have := (abs_le.mp hlogp).2
    unfold hiLogQ; push_cast; linarith
  have hlo' : (loLogQ ((n1 : ℚ) / ((n2 : ℚ) + 1)) N : ℝ) ≤ Real.log (vY lo / vY hi) := by
    have := (abs_le.mp hlogm).1
    unfold loLogQ; push_cast; linarith
  have hmax : (a1 : ℝ) * Real.log (vY lo / vY hi) ≤
      (max ((a1 : ℚ) * hiLogQ (((n1 : ℚ) + 1) / n2) N)
        ((a1 : ℚ) * loLogQ ((n1 : ℚ) / ((n2 : ℚ) + 1)) N) : ℚ) := by
    rw [Rat.cast_max]
    rcases le_total 0 (a1 : ℝ) with h | h
    · refine le_trans ?_ (le_max_left _ _)
      push_cast; exact mul_le_mul_of_nonneg_left hhi h
    · refine le_trans ?_ (le_max_right _ _)
      push_cast; exact mul_le_mul_of_nonpos_left hlo' h
  have hlogdiff : Real.log (vY lo / vY hi) = Real.log (vY lo) - Real.log (vY hi) :=
    Real.log_div hv1.ne' hv2.ne'
  -- assemble
  have q1 := FSq_eq (a := a0) (b := a1) (r := r) hK hd hn1 k
  have q2 := FSq_eq (a := a0) (b := a1) (r := r) hK hd hn2 k
  rw [hI, hF, hF]
  unfold cellUB
  push_cast
  rw [q1, q2]
  rw [hlogdiff] at hmax
  rw [← hz] at q1 q2
  rw [Rat.cast_max] at hmax
  push_cast at hmax
  have f1 := e1.1
  have f2 := e2.2
  linarith [E1, E2, hmax]

/-! ### Dyadic brackets, reflection, and the positive-cell bound for a `YCell` -/

def brk (Y : ℤ) (n k : ℕ) : Bool :=
  decide (0 < n) && decide (n + 1 ≤ 2 ^ k) &&
    decide ((Y : ℚ) / 10 ^ 12 ≤ (n : ℚ) / 2 ^ k + 2 ^ k / n) &&
    decide (((n : ℚ) + 1) / 2 ^ k + 2 ^ k / ((n : ℚ) + 1) ≤ (Y : ℚ) / 10 ^ 12)

theorem brk_sound {Y : ℤ} {n k : ℕ} (h : brk Y n k = true) (hY : 2 ≤ (Y : ℝ) / 10 ^ 12) :
    0 < n ∧ n + 1 ≤ 2 ^ k ∧ (n : ℝ) / 2 ^ k ≤ vY ((Y : ℝ) / 10 ^ 12) ∧
      vY ((Y : ℝ) / 10 ^ 12) ≤ ((n : ℝ) + 1) / 2 ^ k := by
  simp only [brk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hn : (0 : ℝ) < n := by exact_mod_cast h0
  have hS : (0 : ℝ) < 2 ^ k := by positivity
  have h1r : (n : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast h1
  have c2 : (Y : ℝ) / 10 ^ 12 ≤ (n : ℝ) / 2 ^ k + ((n : ℝ) / 2 ^ k)⁻¹ := by
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this
    simpa [inv_div] using this
  have c3 : ((n : ℝ) + 1) / 2 ^ k + (((n : ℝ) + 1) / 2 ^ k)⁻¹ ≤ (Y : ℝ) / 10 ^ 12 := by
    have := (Rat.cast_le (K := ℝ)).mpr h3
    push_cast at this
    simpa [inv_div] using this
  refine ⟨h0, h1, ?_, ?_⟩
  · refine le_vY_of (by positivity) ?_ hY c2
    rw [div_le_one hS]; linarith
  · refine vY_le_of (by positivity) ?_ hY c3
    rw [div_le_one hS]; linarith

def rhoOK (n1 n2 : ℕ) : Bool :=
  decide (0 < n2) && decide (|1 - ((n1 : ℚ) + 1) / n2| < 1) &&
    decide (|1 - (n1 : ℚ) / ((n2 : ℚ) + 1)| < 1)

/-- `z(-x)` as an integer list. -/
def negL : List ℤ → List ℤ
  | [] => []
  | a :: q => a :: smulL (-1) (negL q)

theorem evalZ_negL (z : List ℤ) (x : ℝ) : evalZ (negL z) x = evalZ z (-x) := by
  induction z with
  | nil => simp [negL, evalZ]
  | cons a q ih =>
    simp only [negL, evalZ, evalZ_smulL, ih]
    push_cast; ring

/-- Upper bound for the phys-integral of `evalZ (a0::a1::r)` over a positive cell. -/
theorem pos_phys_le {K a0 a1 : ℤ} {r : List ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ r.length + 2 → (m : ℤ) ∣ K) {B : ℚ}
    (hB : ∀ x ∈ Icc (0 : ℝ) 1, |evalZ (a0 :: a1 :: r) x| ≤ (B : ℝ)) {c : YCell} {Y1 Y2 : ℤ}
    (hc1 : c.lo = (Y1 : ℝ) / 10 ^ 12) (hc2 : c.hi = (Y2 : ℝ) / 10 ^ 12)
    (hY1 : 2 ≤ (Y1 : ℝ) / 10 ^ 12) {k N n1 n2 : ℕ}
    (b1 : brk Y1 n1 k = true) (b2 : brk Y2 n2 k = true) (hr : rhoOK n1 n2 = true) :
    c.phys (evalZ (a0 :: a1 :: r)) ≤
      c.w / (c.hi - c.lo) * (cellUB (Wpoly K a0 a1 r) K a1 B k N n1 n2 : ℝ) := by
  have hlo : 2 ≤ c.lo := by rw [hc1]; exact hY1
  have hY2 : 2 ≤ (Y2 : ℝ) / 10 ^ 12 := by rw [← hc2]; exact hlo.trans c.lo_lt.le
  obtain ⟨hn1, hn1', h1l, h1u⟩ := brk_sound b1 hY1
  obtain ⟨hn2, hn2', h2l, h2u⟩ := brk_sound b2 hY2
  simp only [rhoOK, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨_, hρp⟩, hρm⟩ := hr
  rw [MomentSource.phys_pos hlo]
  have hw : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg (by linarith [c.lo_lt])
  refine mul_le_mul_of_nonneg_left ?_ hw
  have hlt := c.lo_lt.le
  rw [hc1, hc2] at hlt ⊢
  rw [hc1] at hlo
  exact cell_ub hK hd hB hlo hlt hn1 hn2 hn1' hn2' h1l h1u h2l h2u hρp hρm

/-! ### Row cells: the list-level bound -/

def roundUp (x : ℚ) : ℚ := (CatalanMeasure.CellCert.qceil (x * 2 ^ 200) : ℚ) / 2 ^ 200
def roundDown (x : ℚ) : ℚ := (CatalanMeasure.CellCert.qfloor (x * 2 ^ 200) : ℚ) / 2 ^ 200

theorem le_roundUp (x : ℚ) : x ≤ roundUp x := by
  unfold roundUp
  rw [le_div_iff₀ (by positivity)]
  exact CatalanMeasure.CellCert.le_qceil _

theorem roundDown_le (x : ℚ) : roundDown x ≤ x := by
  unfold roundDown
  rw [div_le_iff₀ (by positivity)]
  exact CatalanMeasure.CellCert.qfloor_le _

abbrev Tr := CapSourceData.Tr

def pickZ (z : List ℤ) (a : ℤ) : List ℤ := if 0 ≤ a then z else negL z

theorem length_negL (z : List ℤ) : (negL z).length = z.length := by
  induction z with
  | nil => rfl
  | cons a q ih => simp [negL, smulL, ih]

theorem length_pickZ (z : List ℤ) (a : ℤ) : (pickZ z a).length = z.length := by
  unfold pickZ; split_ifs
  · rfl
  · exact length_negL z

/-- The weight `p 10^12 / (T (b - a))` of a row/column cell. -/
def cellW (T : ℤ) (t : Tr) : ℚ := (t.2.2 : ℚ) * 10 ^ 12 / ((T : ℚ) * ((t.2.1 - t.1 : ℤ) : ℚ))

def rowYs (t : Tr) : ℤ × ℤ := if 0 ≤ t.1 then (t.1, t.2.1) else (-t.2.1, -t.1)

/-- Per-cell bound, with the data `d = (n1, n2)`. -/
def rowTerm (z : List ℤ) (K : ℤ) (B : ℚ) (k N : ℕ) (T : ℤ) (t : Tr) (d : ℕ × ℕ) : ℚ :=
  match pickZ z t.1 with
  | a0 :: a1 :: r => roundUp (cellW T t * cellUB (Wpoly K a0 a1 r) K a1 B k N d.1 d.2)
  | _ => 0

def rowCellOK (z : List ℤ) (t : Tr) (k : ℕ) (d : ℕ × ℕ) : Bool :=
  decide (2 ≤ z.length) && decide (t.1 < t.2.1) && decide (0 ≤ t.2.2) &&
  decide (2 * 10 ^ 12 ≤ (rowYs t).1) && brk (rowYs t).1 d.1 k && brk (rowYs t).2 d.2 k && rhoOK d.1 d.2

def rowSum (z : List ℤ) (K : ℤ) (B : ℚ) (k N : ℕ) (T : ℤ) : List Tr → List (ℕ × ℕ) → ℚ
  | t :: ts, d :: ds => rowTerm z K B k N T t d + rowSum z K B k N T ts ds
  | _, _ => 0

def rowOK (z : List ℤ) (k : ℕ) : List Tr → List (ℕ × ℕ) → Bool
  | [], [] => true
  | t :: ts, d :: ds => rowCellOK z t k d && rowOK z k ts ds
  | _, _ => false

theorem row_cell_le {z : List ℤ} {a0 a1 : ℤ} {r : List ℤ} (hz : z = a0 :: a1 :: r) {K : ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ z.length → (m : ℤ) ∣ K) {B : ℚ}
    (hB : ∀ x ∈ Icc (-1 : ℝ) 1, |evalZ z x| ≤ (B : ℝ)) {T : ℤ} (hT : 0 < T) {t : Tr} {k N : ℕ}
    {d : ℕ × ℕ} (h : rowCellOK z t k d = true) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (CapSourceData.mkCell 1 T t).phys (evalZ z) ≤ (rowTerm z K B k N T t d : ℝ) := by
  obtain ⟨hlt0, hp0⟩ := hv
  have hT0 : (0 : ℤ) ≤ T := hT.le
  obtain ⟨e1, e2, e3⟩ := CapSourceData.mkCell_eq (m := 1) (T := T) (t := t) ⟨hlt0, hp0⟩ hT0 zero_le_one
  set c := CapSourceData.mkCell 1 T t with hc
  simp only [rowCellOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hlen, hlt, hp, haway, b1, b2, hr⟩ := h
  have hba : (0 : ℝ) < ((t.2.1 : ℝ) - t.1) := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hlt0
    linarith
  have hwt : ((cellW T t : ℚ) : ℝ) = c.w / (c.hi - c.lo) := by
    rw [e1, e2, e3]
    unfold cellW
    have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    push_cast
    field_simp
  have hcell : ∀ (x : ℚ), (0 ≤ x) → True := fun _ _ => trivial
  by_cases hs : 0 ≤ t.1
  · subst hz
    have hY : rowYs t = (t.1, t.2.1) := by simp [rowYs, hs]
    rw [hY] at haway b1 b2
    have hpz : pickZ (a0 :: a1 :: r) t.1 = a0 :: a1 :: r := by simp [pickZ, hs]
    have hBx : ∀ x ∈ Icc (0 : ℝ) 1, |evalZ (a0 :: a1 :: r) x| ≤ (B : ℝ) := by
      intro x hx; exact hB x ⟨by linarith [hx.1], hx.2⟩
    have hdr : ∀ m : ℕ, 1 ≤ m → m ≤ r.length + 2 → (m : ℤ) ∣ K := by
      intro m h1 h2; exact hd m h1 (by simpa using h2)
    have hY1 : 2 ≤ ((t.1 : ℤ) : ℝ) / 10 ^ 12 := by
      have : ((2 * 10 ^ 12 : ℤ) : ℝ) ≤ (t.1 : ℝ) := by exact_mod_cast haway
      rw [le_div_iff₀ (by positivity)]; push_cast at this; linarith
    have := pos_phys_le (N := N) hK hdr hBx (c := c) (Y1 := t.1) (Y2 := t.2.1) e1 e2 hY1 b1 b2 hr
    refine this.trans ?_
    unfold rowTerm
    rw [hpz, ← hwt]
    have := le_roundUp (cellW T t * cellUB (Wpoly K a0 a1 r) K a1 B k N d.1 d.2)
    have hr' := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at hr' ⊢
    exact hr'
  · have hs' : t.1 < 0 := by omega
    have hY : rowYs t = (-t.2.1, -t.1) := by simp [rowYs, hs]
    rw [hY] at haway b1 b2
    have hpz : pickZ z t.1 = negL z := by simp [pickZ, hs]
    have hneg : negL z = a0 :: (-1 * a1) :: smulL (-1) (smulL (-1) (negL r)) := by rw [hz]; rfl
    have hch : c.hi ≤ -2 := by
      rw [e2]
      have : ((2 * 10 ^ 12 : ℤ) : ℝ) ≤ ((-t.2.1 : ℤ) : ℝ) := by exact_mod_cast haway
      push_cast at this
      rw [div_le_iff₀ (by positivity)]; linarith
    have href := MomentSource.phys_reflect hch (evalZ z)
    have hfun : (fun x => evalZ z (-x)) = evalZ (a0 :: (-1 * a1) :: smulL (-1) (smulL (-1) (negL r))) := by
      rw [← hneg]; funext x; rw [evalZ_negL]
    rw [hfun] at href
    have hBx : ∀ x ∈ Icc (0 : ℝ) 1,
        |evalZ (a0 :: (-1 * a1) :: smulL (-1) (smulL (-1) (negL r))) x| ≤ (B : ℝ) := by
      intro x hx
      rw [← hneg, evalZ_negL]
      exact hB (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hdr : ∀ m : ℕ, 1 ≤ m → m ≤ (smulL (-1) (smulL (-1) (negL r))).length + 2 → (m : ℤ) ∣ K := by
      intro m h1 h2
      refine hd m h1 ?_
      have : (smulL (-1) (smulL (-1) (negL r))).length = r.length := by simp [smulL, length_negL]
      rw [this] at h2; rw [hz]; simpa using h2
    have hY1 : 2 ≤ ((-t.2.1 : ℤ) : ℝ) / 10 ^ 12 := by
      have : ((2 * 10 ^ 12 : ℤ) : ℝ) ≤ ((-t.2.1 : ℤ) : ℝ) := by exact_mod_cast haway
      rw [le_div_iff₀ (by positivity)]; push_cast at this ⊢; linarith
    have h1 : c.reflect.lo = ((-t.2.1 : ℤ) : ℝ) / 10 ^ 12 := by
      unfold YCell.reflect; simp only; rw [e2]; push_cast; ring
    have h2' : c.reflect.hi = ((-t.1 : ℤ) : ℝ) / 10 ^ 12 := by
      unfold YCell.reflect; simp only; rw [e1]; push_cast; ring
    have key := pos_phys_le (N := N) hK hdr hBx (c := c.reflect) (Y1 := -t.2.1) (Y2 := -t.1) h1 h2' hY1
      b1 b2 hr
    have hwr : c.reflect.w / (c.reflect.hi - c.reflect.lo) = c.w / (c.hi - c.lo) := by
      unfold YCell.reflect; simp only; congr 1; ring
    rw [hwr] at key
    rw [href]
    refine key.trans ?_
    unfold rowTerm
    rw [hpz, hneg, ← hwt]
    have := le_roundUp (cellW T t * cellUB (Wpoly K a0 (-1 * a1) (smulL (-1) (smulL (-1) (negL r)))) K
      (-1 * a1) B k N d.1 d.2)
    have hr' := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at hr' ⊢
    exact hr'

theorem row_sum_le {z : List ℤ} {a0 a1 : ℤ} {r : List ℤ} (hz : z = a0 :: a1 :: r) {K : ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ z.length → (m : ℤ) ∣ K) {B : ℚ}
    (hB : ∀ x ∈ Icc (-1 : ℝ) 1, |evalZ z x| ≤ (B : ℝ)) {T : ℤ} (hT : 0 < T) {k N : ℕ} :
    ∀ (ts : List Tr) (ds : List (ℕ × ℕ)), (∀ t ∈ ts, t.1 < t.2.1 ∧ 0 ≤ t.2.2) → rowOK z k ts ds = true →
    CapFields.physL (ts.map (CapSourceData.mkCell 1 T)) (evalZ z) ≤ (rowSum z K B k N T ts ds : ℝ) := by
  intro ts
  induction ts with
  | nil => intro ds _ h; cases ds <;> simp [rowOK, rowSum, CapFields.physL] at *
  | cons t ts ih =>
    intro ds hv h
    cases ds with
    | nil => simp [rowOK] at h
    | cons d ds =>
      simp only [rowOK, Bool.and_eq_true] at h
      simp only [List.map_cons, CapFields.physL, List.sum_cons, rowSum]
      push_cast
      have h1 := row_cell_le hz hK hd hB hT (N := N) h.1 (hv t (by simp))
      have h2 := ih ds (fun s hs => hv s (by simp [hs])) h.2
      simp only [CapFields.physL] at h2
      linarith

/-! ### Column cells: exact polynomial primitive -/

def Pj : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: q, j, u => (a : ℝ) * u ^ (j + 1) / ((j : ℝ) + 1) + Pj q (j + 1) u

theorem Pj_deriv (q : List ℤ) : ∀ (j : ℕ) (u : ℝ), HasDerivAt (Pj q j) (u ^ j * evalZ q u) u := by
  induction q with
  | nil =>
    intro j u
    have : Pj [] j = fun _ => (0 : ℝ) := by funext s; simp [Pj]
    rw [this]; simpa [evalZ] using hasDerivAt_const u (0 : ℝ)
  | cons a q ih =>
    intro j u
    have e : Pj (a :: q) j = fun s => (a : ℝ) * s ^ (j + 1) / ((j : ℝ) + 1) + Pj q (j + 1) s := by
      funext s; simp [Pj]
    rw [e]
    have h := (((hasDerivAt_pow (j + 1) u).const_mul (a : ℝ)).div_const ((j : ℝ) + 1)).add (ih (j + 1) u)
    convert h using 1
    simp only [evalZ]
    have : ((j : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem Pj_wJ (K : ℤ) : ∀ (q : List ℤ) (j : ℕ), (∀ m : ℕ, 1 ≤ m → m ≤ j + q.length → (m : ℤ) ∣ K) →
    ∀ u : ℝ, (K : ℝ) * Pj q j u = u ^ (j + 1) * evalZ (wJ K (j + 1) q) u := by
  intro q
  induction q with
  | nil => intro j _ u; simp [Pj, wJ, evalZ]
  | cons a q ih =>
    intro j hd u
    have h1 : ((j + 1 : ℕ) : ℤ) ∣ K := hd (j + 1) (by omega) (by simp only [List.length_cons]; omega)
    have h1' : ((j : ℤ) + 1) ∣ K := by exact_mod_cast h1
    have c1 : (((K / ((j : ℤ) + 1) : ℤ)) : ℝ) = (K : ℝ) / ((j : ℝ) + 1) := by
      have := Int.cast_div (α := ℝ) h1' (by positivity)
      push_cast at this ⊢; exact this
    have ih' := ih (j + 1) (fun m hm1 hm2 => hd m hm1 (by simp only [List.length_cons]; omega)) u
    simp only [Pj, wJ, evalZ]
    rw [mul_add, ih']
    push_cast
    rw [c1]
    have : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem int_evalZ (z : List ℤ) (lo hi : ℝ) :
    ∫ s in lo..hi, evalZ z s = Pj z 0 hi - Pj z 0 lo := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Pj z 0) (f' := fun u => u ^ 0 * evalZ z u)
    (a := lo) (b := hi) (fun u _ => Pj_deriv z 0 u)
    ((continuous_const.mul (continuous_evalZ' z)).intervalIntegrable _ _)
  simpa using this

def colTerm (z : List ℤ) (K : ℤ) (T : ℤ) (t : Tr) : ℚ :=
  let V := wJ K 1 z
  let S : ℕ := 10 ^ 12
  roundDown (cellW T t * (((t.2.1 : ℚ) / S) * (hornS V t.2.1 S : ℚ) / (S : ℚ) ^ V.length -
    ((t.1 : ℚ) / S) * (hornS V t.1 S : ℚ) / (S : ℚ) ^ V.length) / K)

def colSum (z : List ℤ) (K T : ℤ) : List Tr → ℚ
  | [] => 0
  | t :: ts => colTerm z K T t + colSum z K T ts

theorem col_cell_ge {z : List ℤ} {K : ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ z.length → (m : ℤ) ∣ K) {T : ℤ} (hT : 0 < T) {t : Tr}
    (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (colTerm z K T t : ℝ) ≤ (CapSourceData.mkCell 1 T t).avg (evalZ z) := by
  obtain ⟨hlt0, hp0⟩ := hv
  obtain ⟨e1, e2, e3⟩ := CapSourceData.mkCell_eq (m := 1) (T := T) (t := t) ⟨hlt0, hp0⟩ hT.le zero_le_one
  set c := CapSourceData.mkCell 1 T t with hc
  have hba : (0 : ℝ) < ((t.2.1 : ℝ) - t.1) := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hlt0
    linarith
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hS : 0 < 10 ^ 12 := by positivity
  have hd' : ∀ m : ℕ, 1 ≤ m → m ≤ 0 + z.length → (m : ℤ) ∣ K := by simpa using hd
  have hP := Pj_wJ K z 0 hd'
  have hav : c.avg (evalZ z) = c.w / (c.hi - c.lo) * (Pj z 0 c.hi - Pj z 0 c.lo) := by
    unfold YCell.avg; rw [int_evalZ]
  rw [hav]
  have hh : ∀ n : ℤ, (K : ℝ) * Pj z 0 ((n : ℝ) / 10 ^ 12) =
      ((n : ℝ) / 10 ^ 12) * ((hornS (wJ K 1 z) n (10 ^ 12) : ℤ) : ℝ) / ((10 ^ 12 : ℕ) : ℝ) ^ (wJ K 1 z).length := by
    intro n
    rw [hP, zero_add, pow_one, hornS_eq (wJ K 1 z) n hS]
    push_cast
    field_simp <;> norm_num
  have hPa : Pj z 0 c.lo = ((t.1 : ℝ) / 10 ^ 12) * ((hornS (wJ K 1 z) t.1 (10 ^ 12) : ℤ) : ℝ) /
      ((10 ^ 12 : ℕ) : ℝ) ^ (wJ K 1 z).length / K := by
    rw [e1]; have := hh t.1; field_simp at this ⊢; linarith
  have hPb : Pj z 0 c.hi = ((t.2.1 : ℝ) / 10 ^ 12) * ((hornS (wJ K 1 z) t.2.1 (10 ^ 12) : ℤ) : ℝ) /
      ((10 ^ 12 : ℕ) : ℝ) ^ (wJ K 1 z).length / K := by
    rw [e2]; have := hh t.2.1; field_simp at this ⊢; linarith
  have hwt : ((cellW T t : ℚ) : ℝ) = c.w / (c.hi - c.lo) := by
    rw [e1, e2, e3]
    unfold cellW
    push_cast
    field_simp
  have hval : ((cellW T t * (((t.2.1 : ℚ) / ((10 ^ 12 : ℕ) : ℚ)) * (hornS (wJ K 1 z) t.2.1 (10 ^ 12) : ℚ) /
        ((10 ^ 12 : ℕ) : ℚ) ^ (wJ K 1 z).length -
      ((t.1 : ℚ) / ((10 ^ 12 : ℕ) : ℚ)) * (hornS (wJ K 1 z) t.1 (10 ^ 12) : ℚ) /
        ((10 ^ 12 : ℕ) : ℚ) ^ (wJ K 1 z).length) / K : ℚ) : ℝ) =
      c.w / (c.hi - c.lo) * (Pj z 0 c.hi - Pj z 0 c.lo) := by
    rw [hPa, hPb, ← hwt]
    push_cast
    ring
  unfold colTerm
  simp only
  rw [← hval]
  exact_mod_cast roundDown_le _

theorem col_sum_ge {z : List ℤ} {K : ℤ} (hK : 0 < K)
    (hd : ∀ m : ℕ, 1 ≤ m → m ≤ z.length → (m : ℤ) ∣ K) {T : ℤ} (hT : 0 < T) :
    ∀ ts : List Tr, (∀ t ∈ ts, t.1 < t.2.1 ∧ 0 ≤ t.2.2) →
    (colSum z K T ts : ℝ) ≤ ((ts.map (CapSourceData.mkCell 1 T)).map fun c => c.avg (evalZ z)).sum := by
  intro ts
  induction ts with
  | nil => intro _; simp [colSum]
  | cons t ts ih =>
    intro hv
    simp only [colSum, List.map_cons, List.sum_cons]
    push_cast
    have := col_cell_ge hK hd hT (hv t (by simp))
    have := ih (fun s hs => hv s (by simp [hs]))
    linarith

/-! ### Linearity of the cell functionals over finite sums -/

theorem phys_finsum_pos {c : YCell} (hc : 2 ≤ c.lo) {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) :
    c.phys (fun x => ∑ i ∈ s, α i * g i x) = ∑ i ∈ s, α i * c.phys (g i) := by
  rw [MomentSource.phys_pos hc]
  have hint : ∀ i ∈ s, IntervalIntegrable (fun Y => α i * g i (vY Y)) volume c.lo c.hi := fun i _ =>
    (continuous_const.mul ((hg i).comp vY_continuous)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finset_sum hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, MomentSource.phys_pos hc]
  ring

theorem phys_finsum {c : YCell} (hc : 2 ≤ c.lo ∨ c.hi ≤ -2) {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) :
    c.phys (fun x => ∑ i ∈ s, α i * g i x) = ∑ i ∈ s, α i * c.phys (g i) := by
  rcases hc with h | h
  · exact phys_finsum_pos h s α g hg
  · have hr : 2 ≤ c.reflect.lo := by unfold YCell.reflect; simp only; linarith
    rw [MomentSource.phys_reflect h]
    have := phys_finsum_pos hr s α (fun i x => g i (-x)) (fun i => (hg i).comp continuous_neg)
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MomentSource.phys_reflect h (g i)]

theorem avg_finsum {c : YCell} {ι : Type*} (s : Finset ι) (α : ι → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) :
    c.avg (fun x => ∑ i ∈ s, α i * g i x) = ∑ i ∈ s, α i * c.avg (g i) := by
  unfold YCell.avg
  have hint : ∀ i ∈ s, IntervalIntegrable (fun Y => α i * g i Y) volume c.lo c.hi := fun i _ =>
    (continuous_const.mul (hg i)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finset_sum hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem physL_finsum {L : List YCell} (hL : ∀ c ∈ L, 2 ≤ c.lo ∨ c.hi ≤ -2) {ι : Type*}
    (s : Finset ι) (α : ι → ℝ) (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) :
    CapFields.physL L (fun x => ∑ i ∈ s, α i * g i x) = ∑ i ∈ s, α i * CapFields.physL L (g i) := by
  induction L with
  | nil => simp [CapFields.physL]
  | cons c L ih =>
    have h1 := phys_finsum (hL c (by simp)) s α g hg
    have h2 := ih (fun d hd => hL d (by simp [hd]))
    simp only [CapFields.physL, List.map_cons, List.sum_cons] at h2 ⊢
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem colL_finsum (L : List YCell) {ι : Type*} (s : Finset ι) (α : ι → ℝ) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Continuous (g i)) :
    (L.map fun c => c.avg (fun x => ∑ i ∈ s, α i * g i x)).sum =
      ∑ i ∈ s, α i * (L.map fun c => c.avg (g i)).sum := by
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [avg_finsum s α g hg, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-! ### The functional as one polynomial against the anchor cells -/

open CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
  (trialSeqOf weightsOf chebPoly evalZ_chebPoly weightsOf_length weightsOf_getD)

theorem evalZ_eq_sum (l : List ℤ) (x : ℝ) :
    evalZ l x = ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * x ^ i := by
  induction l with
  | nil => simp [evalZ]
  | cons a q ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [evalZ, ih, List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem physL_add {L : List YCell} (hL : ∀ c ∈ L, 2 ≤ c.lo ∨ c.hi ≤ -2) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    CapFields.physL L (fun x => f x + g x) = CapFields.physL L f + CapFields.physL L g := by
  have := physL_finsum hL (Finset.univ : Finset Bool) (fun _ => (1 : ℝ))
    (fun b => if b then f else g) (by intro b; cases b <;> simp [hf, hg])
  simpa [Fintype.sum_bool, add_comm] using this

def zRof (Lc : ℤ) (la lv : List ℤ) : List ℤ :=
  addL (smulL 2 (chebPoly 0 (weightsOf Lc la))) (0 :: weightsOf Lc lv)

def zCof (Lc : ℤ) (lv : List ℤ) : List ℤ := chebPoly 0 (weightsOf Lc lv)

theorem castdiv {Lc : ℤ} {i : ℕ} (h : ((i : ℤ) + 1) ∣ Lc) :
    (((Lc / ((i : ℤ) + 1) : ℤ)) : ℝ) = (Lc : ℝ) / ((i : ℝ) + 1) := by
  have := Int.cast_div (α := ℝ) h (by positivity)
  push_cast at this ⊢; exact this

theorem evalZ_cheb_sum (Lc : ℤ) (l : List ℤ) (hdiv : ∀ i < l.length, ((i : ℤ) + 1) ∣ Lc) (x : ℝ) :
    evalZ (chebPoly 0 (weightsOf Lc l)) x =
      ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x := by
  rw [evalZ_chebPoly, weightsOf_length]
  simp only [Int.cast_zero, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < l.length := Finset.mem_range.mp hi
  rw [weightsOf_getD Lc l hi']
  push_cast
  rw [castdiv (hdiv i hi')]

theorem evalZ_pow_sum (Lc : ℤ) (l : List ℤ) (hdiv : ∀ i < l.length, ((i : ℤ) + 1) ∣ Lc) (x : ℝ) :
    evalZ (0 :: weightsOf Lc l) x =
      ∑ i ∈ Finset.range l.length, (l.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * x ^ (i + 1) := by
  simp only [evalZ, Int.cast_zero, zero_add]
  rw [evalZ_eq_sum, weightsOf_length, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < l.length := Finset.mem_range.mp hi
  rw [weightsOf_getD Lc l hi']
  push_cast
  rw [castdiv (hdiv i hi')]
  ring

theorem barrierInner_trial (u : ℕ → ℝ) (l : List ℤ) (D : ℕ) :
    CompletedGas.barrierInner u (trialSeqOf l D) =
      ∑ k ∈ Finset.range l.length, u (k + 1) * ((l.getD k 0 : ℝ) / D) / ((k + 1 : ℕ) : ℝ) := by
  unfold CompletedGas.barrierInner
  apply tsum_eq_sum
  intro k hk
  have hlen : l.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  have h0 : l.getD k 0 = 0 := List.getD_eq_default l 0 hlen
  have : trialSeqOf l D (k + 1) = 0 := by
    simp [trialSeqOf]; left; simpa [List.getD_eq_getElem?_getD] using h0
  rw [this]; simp

theorem inner_eq {R C : List YCell} (hR : ∀ c ∈ R, 2 ≤ c.lo ∨ c.hi ≤ -2) {Lc : ℤ} {D : ℕ}
    (hD : 0 < D) (hLc : 0 < Lc)
    {la lv : List ℤ} (hn : la.length = lv.length)
    (hdiv : ∀ i < la.length, ((i : ℤ) + 1) ∣ Lc) :
    2 * CompletedGas.barrierInner (CompletedGas.rowT R) (trialSeqOf la D) +
      CompletedGas.barrierInner (CompletedGas.anchorV R C) (trialSeqOf lv D) =
    (CapFields.physL R (evalZ (zRof Lc la lv)) -
      2 * (C.map fun c => c.avg (evalZ (zCof Lc lv))).sum) / ((D : ℝ) * Lc) := by
  have hdiv' : ∀ i < lv.length, ((i : ℤ) + 1) ∣ Lc := by rw [← hn]; exact hdiv
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hLr : (Lc : ℝ) ≠ 0 := by exact_mod_cast hLc.ne'
  have hcT : ∀ k : ℕ, Continuous fun u : ℝ => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).eval u :=
    fun k => (Polynomial.Chebyshev.T ℝ ((k : ℕ) : ℤ)).continuous
  have hcP : ∀ k : ℕ, Continuous fun u : ℝ => u ^ k := fun k => continuous_pow k
  rw [barrierInner_trial, barrierInner_trial]
  have pR : ∀ x : ℝ, evalZ (zRof Lc la lv) x =
      (∑ i ∈ Finset.range la.length, (la.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * 2 *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x) +
      ∑ i ∈ Finset.range lv.length, (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * x ^ (i + 1) := by
    intro x
    unfold zRof
    rw [evalZ_addL, evalZ_smulL, evalZ_cheb_sum Lc la hdiv, evalZ_pow_sum Lc lv hdiv', Finset.mul_sum]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have pC : ∀ x : ℝ, evalZ (zCof Lc lv) x =
      ∑ i ∈ Finset.range lv.length, (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x := fun x => evalZ_cheb_sum Lc lv hdiv' x
  have fT : Continuous fun x : ℝ => ∑ i ∈ Finset.range la.length,
      (la.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * 2 *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul (hcT (i + 1))
  have fP : Continuous fun x : ℝ => ∑ i ∈ Finset.range lv.length,
      (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * x ^ (i + 1) := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul (hcP (i + 1))
  have e1 : CapFields.physL R (evalZ (zRof Lc la lv)) =
      ∑ i ∈ Finset.range la.length, (la.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * 2 *
        CompletedGas.rowT R (i + 1) +
      ∑ i ∈ Finset.range lv.length, (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) *
        CompletedGas.rowB R (i + 1) := by
    have : evalZ (zRof Lc la lv) = fun x => (∑ i ∈ Finset.range la.length,
        (la.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * 2 *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x) +
      ∑ i ∈ Finset.range lv.length, (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * x ^ (i + 1) :=
      funext pR
    rw [this, physL_add hR fT fP,
      physL_finsum hR (Finset.range la.length)
        (fun i => (la.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) * 2)
        (fun i x => (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x) (fun i => hcT (i + 1)),
      physL_finsum hR (Finset.range lv.length)
        (fun i => (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)))
        (fun i x => x ^ (i + 1)) (fun i => hcP (i + 1))]
    rfl
  have e2 : (C.map fun c => c.avg (evalZ (zCof Lc lv))).sum =
      ∑ i ∈ Finset.range lv.length, (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) *
        CompletedGas.colT C (i + 1) := by
    have : evalZ (zCof Lc lv) = fun x => ∑ i ∈ Finset.range lv.length,
        (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)) *
        (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x := funext pC
    rw [this, colL_finsum C (Finset.range lv.length)
      (fun i => (lv.getD i 0 : ℝ) * ((Lc : ℝ) / ((i : ℝ) + 1)))
      (fun i x => (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x) (fun i => hcT (i + 1))]
    rfl
  rw [e1, e2, ← hn]
  simp only [CompletedGas.anchorV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-! ### The assembled enclosure -/

/-- `∑ |l_i|` as a rational. -/
def l1S (l : List ℤ) : ℚ := ∑ i ∈ Finset.range l.length, |((l.getD i 0 : ℤ) : ℚ)|

theorem abs_cheb_le (l : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |evalZ (chebPoly 0 l) x| ≤ (l1S l : ℝ) := by
  rw [evalZ_chebPoly]
  simp only [Int.cast_zero, zero_add, l1S]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc _ ≤ |(l.getD i 0 : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (Polynomial.Chebyshev.abs_eval_T_real_le_one _ hx) (abs_nonneg _)
    _ = _ := mul_one _

theorem abs_sum_le (l : List ℤ) {x : ℝ} (hx : |x| ≤ 1) : |evalZ l x| ≤ (l1S l : ℝ) := by
  rw [evalZ_eq_sum]
  simp only [l1S]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow]
  calc _ ≤ |(l.getD i 0 : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx) (abs_nonneg _)
    _ = _ := mul_one _

def BRof (Lc : ℤ) (la lv : List ℤ) : ℚ := 2 * l1S (weightsOf Lc la) + l1S (weightsOf Lc lv)

theorem bound_zR (Lc : ℤ) (la lv : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |evalZ (zRof Lc la lv) x| ≤ (BRof Lc la lv : ℝ) := by
  unfold zRof BRof
  rw [evalZ_addL, evalZ_smulL]
  have h1 := abs_cheb_le (weightsOf Lc la) hx
  have h2 : |evalZ (0 :: weightsOf Lc lv) x| ≤ (l1S (weightsOf Lc lv) : ℝ) := by
    simp only [evalZ, Int.cast_zero, zero_add]
    rw [abs_mul]
    calc _ ≤ 1 * (l1S (weightsOf Lc lv) : ℝ) :=
          mul_le_mul hx (abs_sum_le _ hx) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  calc _ ≤ |((2 : ℤ) : ℝ) * evalZ (chebPoly 0 (weightsOf Lc la)) x| + |evalZ (0 :: weightsOf Lc lv) x| :=
        abs_add_le _ _
    _ ≤ 2 * (l1S (weightsOf Lc la) : ℝ) + (l1S (weightsOf Lc lv) : ℝ) := by
        rw [abs_mul]; push_cast
        have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
        rw [this]
        linarith
    _ = _ := by push_cast; ring

theorem bound_zC (Lc : ℤ) (lv : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |evalZ (zCof Lc lv) x| ≤ (l1S (weightsOf Lc lv) : ℝ) := abs_cheb_le _ hx

theorem refRow_cells : ∀ c ∈ CapSourceData.refRowF 0, 2 ≤ c.lo ∨ c.hi ≤ -2 := by
  intro c hc
  have : CapSourceData.refRowF 0 = CapSourceData.row0.map (CapSourceData.mkCell 1 (CapSourceData.sumP CapSourceData.row0)) := by
    simp [CapSourceData.refRowF]
  rw [this] at hc
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
  by_cases hnn : 0 ≤ t.1
  · exact Or.inl (CapSourceData.cell_lo_ge (CapSourceData.row0_ok t ht) CapSourceData.row0_tot.le
      zero_le_one ((CapSourceData.row0_away t ht).1 hnn))
  · exact Or.inr (CapSourceData.cell_hi_le (CapSourceData.row0_ok t ht) CapSourceData.row0_tot.le
      zero_le_one ((CapSourceData.row0_away t ht).2 (by omega)))

theorem E2_bound {la lv : List ℤ} {D : ℕ} {Lc : ℤ} (hD : 0 < D) (hLc : 0 < Lc)
    (hn : la.length = lv.length)
    (h140 : ∀ m : ℕ, 1 ≤ m → m ≤ 140 → (m : ℤ) ∣ Lc)
    (hlenR : (zRof Lc la lv).length ≤ 140) (hlenC : (zCof Lc lv).length ≤ 140)
    (hla : la.length ≤ 140) {k N : ℕ} {dat : List (ℕ × ℕ)}
    (hrow : rowOK (zRof Lc la lv) k CapSourceData.row0 dat = true)
    (hlenR2 : 2 ≤ (zRof Lc la lv).length) (hlenC2 : 2 ≤ (zCof Lc lv).length) :
    2 * CompletedGas.barrierInner (CompletedGas.rowT (CapSourceData.refRowF 0)) (trialSeqOf la D) +
      CompletedGas.barrierInner (CompletedGas.anchorV (CapSourceData.refRowF 0) (CapSourceData.refColF 0))
        (trialSeqOf lv D) ≤
    ((rowSum (zRof Lc la lv) Lc (BRof Lc la lv) k N (CapSourceData.sumP CapSourceData.row0)
        CapSourceData.row0 dat -
      2 * colSum (zCof Lc lv) Lc (CapSourceData.sumP CapSourceData.col0) CapSourceData.col0 : ℚ) : ℝ)
      / ((D : ℝ) * Lc) := by
  have hdiv : ∀ i < la.length, ((i : ℤ) + 1) ∣ Lc := by
    intro i hi
    have := h140 (i + 1) (by omega) (by omega)
    simpa using this
  rw [inner_eq refRow_cells hD hLc hn hdiv]
  have hpos : (0 : ℝ) < (D : ℝ) * Lc := by
    have : (0 : ℝ) < Lc := by exact_mod_cast hLc
    have : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  apply div_le_div_of_nonneg_right _ hpos.le
  obtain ⟨a0, a1, r, hz⟩ : ∃ a0 a1 r, zRof Lc la lv = a0 :: a1 :: r := by
    match h : zRof Lc la lv, hlenR2 with
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  have hR : CapFields.physL (CapSourceData.refRowF 0) (evalZ (zRof Lc la lv)) ≤
      (rowSum (zRof Lc la lv) Lc (BRof Lc la lv) k N (CapSourceData.sumP CapSourceData.row0)
        CapSourceData.row0 dat : ℝ) := by
    have : CapSourceData.refRowF 0 = CapSourceData.row0.map (CapSourceData.mkCell 1 (CapSourceData.sumP CapSourceData.row0)) := by
      simp [CapSourceData.refRowF]
    rw [this]
    refine row_sum_le hz hLc (fun m h1 h2 => h140 m h1 (by omega)) (fun x hx => ?_)
      (T := CapSourceData.sumP CapSourceData.row0) CapSourceData.row0_tot CapSourceData.row0 dat
      (fun t ht => CapSourceData.row0_ok t ht) hrow
    exact bound_zR Lc la lv (abs_le.mpr ⟨hx.1, hx.2⟩)
  have hC : (colSum (zCof Lc lv) Lc (CapSourceData.sumP CapSourceData.col0) CapSourceData.col0 : ℝ) ≤
      ((CapSourceData.refColF 0).map fun c => c.avg (evalZ (zCof Lc lv))).sum := by
    have : CapSourceData.refColF 0 = CapSourceData.col0.map (CapSourceData.mkCell 1 (CapSourceData.sumP CapSourceData.col0)) := by
      simp [CapSourceData.refColF]
    rw [this]
    exact col_sum_ge hLc (fun m h1 h2 => h140 m h1 (by omega)) CapSourceData.col0_tot CapSourceData.col0
      (fun t ht => CapSourceData.col0_ok t ht)
  push_cast
  linarith

end
end CatalanMeasure.GenD.Signed.RouteI.AnchorE2
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.cell_ub
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.row_cell_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.row_sum_le
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.col_sum_ge
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.inner_eq
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.E2_bound
#print axioms CatalanMeasure.GenD.Signed.RouteI.AnchorE2.bound_zR
