module

public import CatalanMeasure.GenD.Signed.RouteI.FreeColCap0
public import CatalanMeasure.CellCert.RawInts

/-!
# Anchor-0 free column cap by polynomial units

Finite checks to `capSource.FreeColCap 0 (-2946610/1000000)`, the input `hC` of T4.

On a unit `s = (M + δ z)/10^12`, `z ∈ [-1,1]`, the field is bounded above by an integer polynomial
in `z` over `2^64` plus an integer error. Far source cells enter through exact integer moments of
contiguous clusters and the Taylor series of the logarithmic kernel (`clu_abs`, `tile_up`). Near
column cells enter through the closed form of their potential, one node per cell end (`nodes_sum`,
`n_up`). The two logarithms of the field enter by series or, on end units, by monotonicity. The
constant is `L_cert`. `freeColCap_of_units` is the generic consumer. `UB_cap` is one real unit: it
contains the measured supremum of the field.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false

namespace CatalanMeasure.GenD.Signed.RouteI.FreeColCert

open Real Set intervalIntegral MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.FreeColCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot (lnormOK)

/-! ### Integer polynomials on `[-1,1]` -/

def addL : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a :: l, [] => a :: l
  | a :: l, b :: r => (a + b) :: addL l r

noncomputable def evalZ : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, z => (a : ℝ) + z * evalZ l z

theorem evalZ_addL : ∀ (a b : List ℤ) (z : ℝ), evalZ (addL a b) z = evalZ a z + evalZ b z
  | [], b, z => by simp [addL, evalZ]
  | a :: l, [], z => by simp [addL, evalZ]
  | a :: l, b :: r, z => by
    simp only [addL, evalZ, evalZ_addL l r z]; push_cast; ring

/-- bound of the even-position tail. -/
def bE : List ℤ → ℤ
  | [] => 0
  | a :: l => max a 0 + (match l with
      | [] => 0
      | b :: r => |b| + bE r)

theorem bE_nonneg : ∀ l : List ℤ, 0 ≤ bE l
  | [] => by simp [bE]
  | a :: [] => by simp [bE]
  | a :: b :: r => by
    have := bE_nonneg r
    simp only [bE]
    have h1 : 0 ≤ max a 0 := le_max_right _ _
    have h2 := abs_nonneg b
    omega

theorem evalZ_le_bE : ∀ (l : List ℤ) (z : ℝ), |z| ≤ 1 → evalZ l z ≤ (bE l : ℝ)
  | [], z, _ => by simp [evalZ, bE]
  | a :: [], z, _ => by
    simp only [evalZ, bE, mul_zero, add_zero]
    exact_mod_cast le_max_left a 0
  | a :: b :: r, z, hz => by
    have ih := evalZ_le_bE r z hz
    have h0 : (0:ℝ) ≤ bE r := by exact_mod_cast bE_nonneg r
    have hz2 : z * z ≤ 1 := by nlinarith [abs_le.1 hz, sq_abs z]
    have hz0 : 0 ≤ z * z := mul_self_nonneg z
    simp only [evalZ, bE]
    push_cast
    have ha : (a : ℝ) ≤ max (a:ℝ) 0 := le_max_left _ _
    have hb : z * b ≤ |(b : ℝ)| := by
      calc z * b ≤ |z * b| := le_abs_self _
        _ = |z| * |(b:ℝ)| := abs_mul _ _
        _ ≤ 1 * |(b:ℝ)| := by gcongr
        _ = _ := one_mul _
    have hc : z * z * evalZ r z ≤ (bE r : ℝ) := by
      calc z * z * evalZ r z ≤ z * z * (bE r : ℝ) := by gcongr
        _ ≤ 1 * (bE r : ℝ) := by gcongr
        _ = _ := one_mul _
    nlinarith

/-- `Up Z f Q e`: on `Z`, `f <= (Q(z) + e)/2^64`. -/
def Up (Z : Set ℝ) (f : ℝ → ℝ) (Q : List ℤ) (e : ℤ) : Prop :=
  ∀ z ∈ Z, f z ≤ (evalZ Q z + e) / 2 ^ 64

theorem Up.add {Z : Set ℝ} {f g : ℝ → ℝ} {Q P : List ℤ} {e d : ℤ} (hf : Up Z f Q e)
    (hg : Up Z g P d) : Up Z (fun z => f z + g z) (addL Q P) (e + d) := by
  intro z hz
  have h1 := hf z hz
  have h2 := hg z hz
  rw [evalZ_addL]
  push_cast
  linarith

theorem rnd_abs (a b : ℤ) (hb : b ≠ 0) : |(a : ℝ) / b - ((a / b : ℤ) : ℝ)| ≤ 1 := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt_abs a hb
  have h2 := Int.mul_ediv_add_emod a b
  have e : (a : ℝ) / b - ((a / b : ℤ) : ℝ) = ((a % b : ℤ) : ℝ) / b := by
    have : (a : ℝ) = (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by exact_mod_cast h2.symm
    rw [this]; field_simp; ring_nf
  rw [e, abs_div]
  have h3 : |((a % b : ℤ) : ℝ)| ≤ |(b : ℝ)| := by
    have : |a % b| ≤ |b| := by rw [abs_of_nonneg h0]; exact h1.le
    exact_mod_cast this
  exact (div_le_one (abs_pos.2 hb')).2 h3

/-! ### Logarithm kernel -/

noncomputable def Pl (n : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1)

theorem log1m_abs {x θ : ℝ} (hx : |x| ≤ θ) (hθ : θ < 1) (n : ℕ) :
    |Real.log (1 - x) + Pl n x| ≤ θ ^ (n + 1) / (1 - θ) := by
  have hx1 : |x| < 1 := lt_of_le_of_lt hx hθ
  have h := Real.abs_log_sub_add_sum_range_le hx1 n
  have e : (∑ i ∈ Finset.range n, x ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - x) =
      Real.log (1 - x) + Pl n x := by unfold Pl; ring
  rw [e] at h
  refine h.trans ?_
  have h0 : 0 ≤ |x| := abs_nonneg x
  have h1 : 0 ≤ θ := h0.trans hx
  have : 0 < 1 - θ := by linarith
  gcongr

/-- `log|T(1-x)|` expansion. -/
theorem logT_abs {T x θ : ℝ} (hT : T ≠ 0) (hx : |x| ≤ θ) (hθ : θ < 1) (n : ℕ) :
    |Real.log |T * (1 - x)| - (Real.log |T| - Pl n x)| ≤ θ ^ (n + 1) / (1 - θ) := by
  have hx1 : 0 < 1 - x := by have := (abs_le.1 (hx.trans hθ.le)).2; have := abs_lt.1 (lt_of_le_of_lt hx hθ); linarith [this.2]
  have e : Real.log |T * (1 - x)| = Real.log |T| + Real.log (1 - x) := by
    rw [abs_mul, Real.log_mul (abs_ne_zero.2 hT) (abs_ne_zero.2 hx1.ne'), abs_of_pos hx1]
  rw [e]
  have := log1m_abs hx hθ n
  have e2 : Real.log |T| + Real.log (1 - x) - (Real.log |T| - Pl n x) = Real.log (1 - x) + Pl n x := by ring
  rw [e2]; exact this

/-! ### One cell: moments -/

theorem avg_pow (c : YCell) (a : ℝ) (k : ℕ) :
    c.avg (fun t => (t - a) ^ k) =
      c.w / (c.hi - c.lo) * (((c.hi - a) ^ (k + 1) - (c.lo - a) ^ (k + 1)) / ((k : ℝ) + 1)) := by
  unfold YCell.avg
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ k) a, integral_pow]

theorem cell_enc (c : YCell) (a T y θ : ℝ) (hT : T ≠ 0) (hy : y = a + T) (hθ : θ < 1)
    (hr : ∀ t ∈ Icc c.lo c.hi, |(t - a) / T| ≤ θ) (D : ℕ) :
    |c.pot y - (c.w * Real.log |T| -
        ∑ i ∈ Finset.range D, c.avg (fun t => (t - a) ^ (i + 1)) / (((i : ℝ) + 1) * T ^ (i + 1)))| ≤
      c.w * (θ ^ (D + 1) / (1 - θ)) := by
  have hl : c.lo < c.hi := c.lo_lt
  have hd : 0 < c.hi - c.lo := by linarith
  set G : ℝ → ℝ := fun t => Real.log |T| - Pl D ((t - a) / T) with hG
  have hGc : Continuous G := by
    simp only [hG, Pl]
    fun_prop
  have hint : ∫ t in c.lo..c.hi, G t = (c.hi - c.lo) * Real.log |T| -
      ∑ i ∈ Finset.range D, (∫ t in c.lo..c.hi, (t - a) ^ (i + 1)) / (((i : ℝ) + 1) * T ^ (i + 1)) := by
    simp only [hG, Pl]
    rw [intervalIntegral.integral_sub (by simp) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_finset_sum
        (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ t : ℝ, ((t - a) / T) ^ (i + 1) / ((i : ℝ) + 1) =
        (t - a) ^ (i + 1) / (((i : ℝ) + 1) * T ^ (i + 1)) := by
      intro t
      rw [div_pow]; field_simp
    simp only [this]
    rw [intervalIntegral.integral_div]
  have hb : |∫ t in c.lo..c.hi, (Real.log |y - t| - G t)| ≤
      (θ ^ (D + 1) / (1 - θ)) * |c.hi - c.lo| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c.lo) (b := c.hi)
      (f := fun t => Real.log |y - t| - G t) (C := θ ^ (D + 1) / (1 - θ)) ?_
    · simpa [Real.norm_eq_abs] using this
    · intro t ht
      rw [uIoc_of_le hl.le] at ht
      have ht' : t ∈ Icc c.lo c.hi := ⟨ht.1.le, ht.2⟩
      have hx := hr t ht'
      have e : y - t = T * (1 - (t - a) / T) := by rw [hy]; field_simp; ring
      rw [e, Real.norm_eq_abs]
      exact logT_abs hT hx hθ D
  rw [intervalIntegral.integral_sub (FreeColCap0.ii_log _ _ _) (hGc.intervalIntegrable _ _), hint,
    abs_of_pos hd] at hb
  have hw := c.w_nonneg
  have e1 : c.pot y - (c.w * Real.log |T| -
        ∑ i ∈ Finset.range D, c.avg (fun t => (t - a) ^ (i + 1)) / (((i : ℝ) + 1) * T ^ (i + 1))) =
      c.w / (c.hi - c.lo) * ((∫ t in c.lo..c.hi, Real.log |y - t|) - ((c.hi - c.lo) * Real.log |T| -
      ∑ i ∈ Finset.range D, (∫ t in c.lo..c.hi, (t - a) ^ (i + 1)) / (((i : ℝ) + 1) * T ^ (i + 1)))) := by
    unfold YCell.pot YCell.avg
    rw [mul_sub, mul_sub, Finset.mul_sum]
    have : c.w / (c.hi - c.lo) * ((c.hi - c.lo) * Real.log |T|) = c.w * Real.log |T| := by
      field_simp
    rw [this]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ c.w / (c.hi - c.lo))]
  calc c.w / (c.hi - c.lo) * _ ≤ c.w / (c.hi - c.lo) * (θ ^ (D + 1) / (1 - θ) * (c.hi - c.lo)) := by
        gcongr
    _ = _ := by field_simp

/-! ### Integer moments -/

def hj (a b : ℤ) : ℕ → ℤ
  | 0 => 1
  | j + 1 => a * hj a b j + b ^ (j + 1)

theorem hj_mul (a b : ℤ) (j : ℕ) : hj a b j * (b - a) = b ^ (j + 1) - a ^ (j + 1) := by
  induction j with
  | zero => simp [hj]
  | succ j ih =>
    simp only [hj]
    have : (a * hj a b j + b ^ (j + 1)) * (b - a) = a * (hj a b j * (b - a)) + b ^ (j + 1) * (b - a) := by ring
    rw [this, ih]; ring

/-- `S_j = sum_t P_t h_j(a_t, b_t)`. -/
def Sj (l : List Tr) (g : ℤ) (j : ℕ) : ℤ := (l.map fun t => t.2.2 * hj (t.1 - g) (t.2.1 - g) j).sum

abbrev Lam : ℝ := 10 ^ 12

noncomputable def MoE (S : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), ((k + 1).choose r : ℝ) * (-x) ^ r * S (k - r) / Lam ^ (k - r)

theorem binom_diff (a b x : ℝ) (k : ℕ) :
    (b - x) ^ (k + 1) - (a - x) ^ (k + 1) =
      ∑ r ∈ Finset.range (k + 1), ((k + 1).choose r : ℝ) * (-x) ^ r * (b ^ (k + 1 - r) - a ^ (k + 1 - r)) := by
  have h1 : ∀ c : ℝ, (c - x) ^ (k + 1) =
      ∑ r ∈ Finset.range (k + 1 + 1), (-x) ^ r * c ^ (k + 1 - r) * ((k + 1).choose r : ℝ) := by
    intro c
    rw [sub_eq_neg_add, add_pow]
  rw [h1, h1, ← Finset.sum_sub_distrib, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero]
  rw [show ∀ u v w : ℝ, u * 1 * v - u * 1 * v = 0 from fun u v _ => by ring, add_zero] <;> try exact 0
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem avg_cell (t : Tr) (Tot g : ℤ) (x : ℝ) (hv : Vt t) (hT : 0 < Tot) (k : ℕ) :
    (mkCell 1 Tot t).avg (fun u => (u - ((g : ℝ) / Lam + x)) ^ k) =
      1 / ((Tot : ℝ) * ((k : ℝ) + 1)) *
        MoE (fun j => (t.2.2 * hj (t.1 - g) (t.2.1 - g) j : ℤ)) k x := by
  obtain ⟨h1, h2, h3⟩ := mkCell_eq (m := 1) (T := Tot) (t := t) hv hT.le (by norm_num)
  rw [avg_pow, h1, h2, h3]
  have hTr : (Tot : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  set A := t.1 - g with hA
  set B := t.2.1 - g with hB
  have hBA : (B : ℝ) - A ≠ 0 := by
    have : A < B := by have := hv.1; omega
    have : (A : ℝ) < B := by exact_mod_cast this
    linarith
  have e1 : (t.2.1 : ℝ) / 10 ^ 12 - ((g : ℝ) / Lam + x) = (B : ℝ) / Lam - x := by
    rw [hB]; push_cast; ring
  have e2 : (t.1 : ℝ) / 10 ^ 12 - ((g : ℝ) / Lam + x) = (A : ℝ) / Lam - x := by
    rw [hA]; push_cast; ring
  have e3 : (t.2.1 : ℝ) / 10 ^ 12 - (t.1 : ℝ) / 10 ^ 12 = ((B : ℝ) - A) / Lam := by
    rw [hA, hB]; push_cast; ring
  rw [e1, e2, e3, binom_diff]
  unfold MoE
  rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ k := by have := Finset.mem_range.1 hr; omega
  obtain ⟨n, rfl⟩ : ∃ n, k = r + n := ⟨k - r, by omega⟩
  have e4 : r + n + 1 - r = n + 1 := by omega
  have e5 : r + n - r = n := by omega
  rw [e4, e5]
  have hh : (hj A B n : ℝ) * ((B : ℝ) - A) = (B : ℝ) ^ (n + 1) - (A : ℝ) ^ (n + 1) := by
    exact_mod_cast hj_mul A B n
  have hL : (Lam : ℝ) ≠ 0 := by norm_num
  have e6 : ((B : ℝ) / Lam) ^ (n + 1) - ((A : ℝ) / Lam) ^ (n + 1) =
      (hj A B n : ℝ) * ((B : ℝ) - A) / Lam ^ (n + 1) := by
    rw [hh, div_pow, div_pow]; ring
  rw [e6]
  push_cast
  have hk : ((r : ℝ) + n + 1) ≠ 0 := by positivity
  simp only [Lam]
  field_simp
  try ring

theorem MoE_add (a b : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    MoE (fun j => a j + b j) k x = MoE a k x + MoE b k x := by
  unfold MoE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem MoE_zero (k : ℕ) (x : ℝ) : MoE (fun _ => 0) k x = 0 := by
  unfold MoE; simp

theorem list_enc (Tot g : ℤ) (x T y θ : ℝ) (hT : 0 < Tot) (hT0 : T ≠ 0)
    (hy : y = (g : ℝ) / Lam + x + T) (hθ : θ < 1) (D : ℕ) : ∀ (l : List Tr), (∀ t ∈ l, Vt t) →
    (∀ t ∈ l, ∀ u ∈ Icc ((t.1 : ℝ) / 10 ^ 12) ((t.2.1 : ℝ) / 10 ^ 12),
      |(u - ((g : ℝ) / Lam + x)) / T| ≤ θ) →
    |potL (l.map (mkCell 1 Tot)) y - ((Sj l g 0 : ℝ) / Tot * Real.log |T| -
      ∑ i ∈ Finset.range D, MoE (fun j => (Sj l g j : ℝ)) (i + 1) x /
        ((Tot : ℝ) * ((i : ℝ) + 2) * (((i : ℝ) + 1) * T ^ (i + 1))))| ≤
      (Sj l g 0 : ℝ) / Tot * (θ ^ (D + 1) / (1 - θ))
  | [], _, _ => by
    simp only [List.map_nil, potL, Sj, List.sum_nil, Int.cast_zero, zero_div, zero_mul, sub_zero]
    simp only [MoE_zero, zero_div, Finset.sum_const_zero]
    simp
  | t :: l, hv, hr => by
    have ih := list_enc Tot g x T y θ hT hT0 hy hθ D l (fun u hu => hv u (List.mem_cons_of_mem _ hu))
      (fun u hu => hr u (List.mem_cons_of_mem _ hu))
    have hvt := hv t (by simp)
    obtain ⟨h1, h2, h3⟩ := mkCell_eq (m := 1) (T := Tot) (t := t) hvt hT.le (by norm_num)
    have hc := cell_enc (mkCell 1 Tot t) ((g : ℝ) / Lam + x) T y θ hT0 (by rw [hy]) hθ
      (fun u hu => hr t (by simp) u (by rw [h1, h2] at hu; exact hu)) D
    have hTr : (Tot : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    have hS : ∀ j, (Sj (t :: l) g j : ℝ) = ((t.2.2 * hj (t.1 - g) (t.2.1 - g) j : ℤ) : ℝ) + (Sj l g j : ℝ) := by
      intro j; simp [Sj]
    have hpot : potL ((t :: l).map (mkCell 1 Tot)) y = (mkCell 1 Tot t).pot y + potL (l.map (mkCell 1 Tot)) y := by
      simp [potL]
    have hw : (mkCell 1 Tot t).w = (t.2.2 : ℝ) / Tot := by rw [h3]; ring
    have hS0 : (Sj (t :: l) g 0 : ℝ) / Tot = (mkCell 1 Tot t).w + (Sj l g 0 : ℝ) / Tot := by
      rw [hS, hw]; simp [hj]; ring
    have hM : ∀ i : ℕ, MoE (fun j => (Sj (t :: l) g j : ℝ)) (i + 1) x /
        ((Tot : ℝ) * ((i : ℝ) + 2) * (((i : ℝ) + 1) * T ^ (i + 1))) =
        (mkCell 1 Tot t).avg (fun u => (u - ((g : ℝ) / Lam + x)) ^ (i + 1)) / (((i : ℝ) + 1) * T ^ (i + 1)) +
        MoE (fun j => (Sj l g j : ℝ)) (i + 1) x /
        ((Tot : ℝ) * ((i : ℝ) + 2) * (((i : ℝ) + 1) * T ^ (i + 1))) := by
      intro i
      rw [avg_cell t Tot g x hvt hT]
      simp only [hS]
      rw [MoE_add]
      have : ((i : ℝ) + 2) ≠ 0 := by positivity
      have : ((i : ℝ) + 1) ≠ 0 := by positivity
      have : T ^ (i + 1) ≠ 0 := pow_ne_zero _ hT0
      push_cast
      field_simp
      ring
    simp only [hM, Finset.sum_add_distrib]
    rw [hpot, hS0]
    have e : ∀ a b p q L s1 s2 : ℝ, a + b - ((p + q) * L - (s1 + s2)) =
        (a - (p * L - s1)) + (b - (q * L - s2)) := by intros; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add hc ih

/-! ### The polynomial table -/

/-- Horner over an implicit list of products. -/
def hz (T : ℤ) : ℕ → List ℤ → List ℤ → ℤ → ℤ
  | 0, _, _, acc => acc
  | n + 1, c :: C, s :: S, acc => hz T n C S (acc * T + c * s)
  | _ + 1, _, _, acc => acc

theorem hz_spec (T : ℤ) : ∀ (n : ℕ) (C S : List ℤ) (acc : ℤ), n ≤ C.length → n ≤ S.length →
    hz T n C S acc = acc * T ^ n +
      ∑ j ∈ Finset.range n, C.getD j 0 * S.getD j 0 * T ^ (n - 1 - j)
  | 0, _, _, acc, _, _ => by simp [hz]
  | n + 1, [], _, acc, h, _ => by simp at h
  | n + 1, _ :: _, [], acc, _, h => by simp at h
  | n + 1, c :: C, s :: S, acc, h1, h2 => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h1 h2
    simp only [hz]
    rw [hz_spec T n C S _ h1 h2, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have : ∀ j ∈ Finset.range n, C.getD j 0 * S.getD j 0 * T ^ (n + 1 - 1 - (j + 1)) =
        C.getD j 0 * S.getD j 0 * T ^ (n - 1 - j) := by
      intro j _
      congr 2
      omega
    rw [Finset.sum_congr rfl this]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    ring

/-- Rounded coefficient list. -/
def qs (T : ℤ) (Sl : List ℤ) (num Dn dl : ℤ) : ℕ → ℤ → List (List ℤ) → List ℤ
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | n + 1, pw, row :: rows =>
    ((num * pw * hz T (n + 1) row Sl 0) / Dn) :: qs T Sl num Dn dl n (pw * dl) rows

theorem qs_abs (T : ℤ) (Sl : List ℤ) (num Dn dl : ℤ) (hD : Dn ≠ 0) {z : ℝ} (hz1 : |z| ≤ 1) :
    ∀ (n : ℕ) (pw : ℤ) (rows : List (List ℤ)) (f : ℕ → ℝ), n ≤ rows.length →
    (∀ m < n, f m = ((num * pw * dl ^ m * hz T (n - m) (rows.getD m []) Sl 0 : ℤ) : ℝ) / Dn) →
    |evalZ (qs T Sl num Dn dl n pw rows) z - ∑ m ∈ Finset.range n, f m * z ^ m| ≤ n
  | 0, _, _, _, _, _ => by simp [qs, evalZ]
  | n + 1, pw, [], _, h, _ => by simp at h
  | n + 1, pw, row :: rows, f, h, hf => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have ih := qs_abs T Sl num Dn dl hD hz1 n (pw * dl) rows (fun m => f (m + 1)) h (by
      intro m hm
      rw [hf (m + 1) (by omega)]
      simp only [List.getD_cons_succ]
      have : n + 1 - (m + 1) = n - m := by omega
      rw [this]
      congr 2
      ring)
    have h0 := hf 0 (by omega)
    simp only [pow_zero, mul_one, List.getD_cons_zero, Nat.sub_zero] at h0
    simp only [qs, evalZ]
    rw [Finset.sum_range_succ']
    have e : ∑ k ∈ Finset.range n, f (k + 1) * z ^ (k + 1) =
        z * ∑ k ∈ Finset.range n, f (k + 1) * z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, h0]
    simp only [pow_zero, mul_one]
    have r := rnd_abs (num * pw * hz T (n + 1) row Sl 0) Dn hD
    set A : ℝ := ((num * pw * hz T (n + 1) row Sl 0 / Dn : ℤ) : ℝ)
    set B : ℝ := ((num * pw * hz T (n + 1) row Sl 0 : ℤ) : ℝ) / (Dn : ℝ)
    set E := evalZ (qs T Sl num Dn dl n (pw * dl) rows) z
    set F := ∑ k ∈ Finset.range n, f (k + 1) * z ^ k
    have e2 : A + z * E - (z * F + B) = (A - B) + z * (E - F) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h3 : |A - B| ≤ 1 := by rw [abs_sub_comm]; exact r
    have h4 : |z| * |E - F| ≤ 1 * n := by
      gcongr
    push_cast
    linarith

/-- GD6: the tables are indexed up to `DM`; `LcT` is the least common multiple of `1, ..., DM + 1`
(80313433200 at `DM = 26`), computed, not stored. -/
def DM : ℕ := 26
def LcT : ℤ := (((List.range (DM + 1)).foldl (fun a i => Nat.lcm a (i + 1)) 1 : ℕ) : ℤ)
def rowsT : List (List ℤ) := [
  raw_ints% [0, 40156716600, 13385572200, 6692786100, 4015671660, 2677114440, 1912224600, 1434168450, 1115464350, 892371480, 730122120, 608435100, 514829700, 441282600, 382444920, 334639305, 295269975, 262462200, 234834600, 211351140, 191222460, 173838600, 158722200, 145495350, 133855722, 123559128, 114406600],
  raw_ints% [80313433200, 40156716600, 26771144400, 20078358300, 16062686640, 13385572200, 11473347600, 10039179150, 8923714800, 8031343320, 7301221200, 6692786100, 6177956400, 5736673800, 5354228880, 5019589575, 4724319600, 4461857400, 4227022800, 4015671660, 3824449200, 3650610600, 3491888400, 3346393050, 3212537328, 3088978200],
  raw_ints% [40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600, 40156716600],
  raw_ints% [26771144400, 40156716600, 53542288800, 66927861000, 80313433200, 93699005400, 107084577600, 120470149800, 133855722000, 147241294200, 160626866400, 174012438600, 187398010800, 200783583000, 214169155200, 227554727400, 240940299600, 254325871800, 267711444000, 281097016200, 294482588400, 307868160600, 321253732800, 334639305000],
  raw_ints% [20078358300, 40156716600, 66927861000, 100391791500, 140548508100, 187398010800, 240940299600, 301175374500, 368103235500, 441723882600, 522037315800, 609043535100, 702742540500, 803134332000, 910218909600, 1023996273300, 1144466423100, 1271629359000, 1405485081000, 1546033589100, 1693274883300, 1847208963600, 2007835830000],
  raw_ints% [16062686640, 40156716600, 80313433200, 140548508100, 224877612960, 337316419440, 481880599200, 662585823900, 883447765200, 1148482094760, 1461704484240, 1827130605300, 2248776129600, 2730656728800, 3276788074560, 3891185838540, 4577865692400, 5340843307800, 6184134356400, 7111754509860, 8127719439840, 9236044818000],
  raw_ints% [13385572200, 40156716600, 93699005400, 187398010800, 337316419440, 562194032400, 883447765200, 1325171647800, 1914136824600, 2679791554440, 3654261210600, 4872348280800, 6371532367200, 8191970186400, 10376495569440, 12970619461800, 16022529923400, 19583092128600, 23705848366200, 28447018039440, 33865497666000],
  raw_ints% [11473347600, 40156716600, 107084577600, 240940299600, 481880599200, 883447765200, 1514481883200, 2461033060200, 3828273649200, 5742410473800, 8352597052800, 11832845824800, 16383940372800, 22235347648800, 29647130198400, 38911858385400, 50356522616400, 64344445565400, 81277194398400, 101596492998000],
  raw_ints% [10039179150, 40156716600, 120470149800, 301175374500, 662585823900, 1325171647800, 2461033060200, 4306807855350, 7178013092250, 11484820947600, 17749268737200, 26623903105800, 38911858385400, 55588369122000, 77823716770800, 107007610559850, 144775002522150, 193033336696200, 253991232495000],
  raw_ints% [8923714800, 40156716600, 133855722000, 368103235500, 883447765200, 1914136824600, 3828273649200, 7178013092250, 12760912164000, 21693550678800, 35498537474400, 56206017667800, 86470796412000, 129706194618000, 190235752106400, 273463893652950, 386066673392400, 536203713045000],
  raw_ints% [8031343320, 40156716600, 147241294200, 441723882600, 1148482094760, 2679791554440, 5742410473800, 11484820947600, 21693550678800, 39048391221840, 67447221201360, 112412035335600, 181588672465200, 285353628159600, 437542229844720, 656313344767080, 965166683481000],
  raw_ints% [7301221200, 40156716600, 160626866400, 522037315800, 1461704484240, 3654261210600, 8352597052800, 17749268737200, 35498537474400, 67447221201360, 122631311275200, 214604794731600, 363177344930400, 596648495242800, 954637592388480, 1491621238107000],
  raw_ints% [6692786100, 40156716600, 174012438600, 609043535100, 1827130605300, 4872348280800, 11832845824800, 26623903105800, 56206017667800, 112412035335600, 214604794731600, 393442123674600, 696089911116600, 1193296990485600, 1988828317476000],
  raw_ints% [6177956400, 40156716600, 187398010800, 702742540500, 2248776129600, 6371532367200, 16383940372800, 38911858385400, 86470796412000, 181588672465200, 363177344930400, 696089911116600, 1285089066676800, 2294801904780000],
  raw_ints% [5736673800, 40156716600, 200783583000, 803134332000, 2730656728800, 8191970186400, 22235347648800, 55588369122000, 129706194618000, 285353628159600, 596648495242800, 1193296990485600, 2294801904780000],
  raw_ints% [5354228880, 40156716600, 214169155200, 910218909600, 3276788074560, 10376495569440, 29647130198400, 77823716770800, 190235752106400, 437542229844720, 954637592388480, 1988828317476000],
  raw_ints% [5019589575, 40156716600, 227554727400, 1023996273300, 3891185838540, 12970619461800, 38911858385400, 107007610559850, 273463893652950, 656313344767080, 1491621238107000],
  raw_ints% [4724319600, 40156716600, 240940299600, 1144466423100, 4577865692400, 16022529923400, 50356522616400, 144775002522150, 386066673392400, 965166683481000],
  raw_ints% [4461857400, 40156716600, 254325871800, 1271629359000, 5340843307800, 19583092128600, 64344445565400, 193033336696200, 536203713045000],
  raw_ints% [4227022800, 40156716600, 267711444000, 1405485081000, 6184134356400, 23705848366200, 81277194398400, 253991232495000],
  raw_ints% [4015671660, 40156716600, 281097016200, 1546033589100, 7111754509860, 28447018039440, 101596492998000],
  raw_ints% [3824449200, 40156716600, 294482588400, 1693274883300, 8127719439840, 33865497666000],
  raw_ints% [3650610600, 40156716600, 307868160600, 1847208963600, 9236044818000],
  raw_ints% [3491888400, 40156716600, 321253732800, 2007835830000],
  raw_ints% [3346393050, 40156716600, 334639305000],
  raw_ints% [3212537328, 40156716600],
  raw_ints% [3088978200]
]

def Rr (i j : ℕ) : ℤ := (rowsT.getD i []).getD j 0

def rowsChk : Bool := (List.range (DM + 1)).all fun i => (List.range (DM + 1 - i)).all fun j =>
  if i + j = 0 then Rr i j == 0 else
    Rr i j * (((i + j) * (i + j + 1) : ℕ) : ℤ) ==
      LcT * ((((i + j + 1).descFactorial i) / i.factorial : ℕ) : ℤ)

theorem rowsChk_true : rowsChk = true := by
  -- kcost: 378 table entries, about 30 small steps each; measured below 1 s
  decide +kernel

theorem rows_len : DM + 1 ≤ rowsT.length := by
  -- kcost: length of a 27 row literal
  decide +kernel

def rowsLenChk : Bool := (List.range (DM + 1)).all fun i => decide (DM + 1 - i ≤ (rowsT.getD i []).length)

theorem rowsLenChk_true : rowsLenChk = true := by
  -- kcost: 27 row lengths
  decide +kernel

theorem rows_len2 {i : ℕ} (h : i ≤ DM) : DM + 1 - i ≤ (rowsT.getD i []).length := by
  have hc := rowsLenChk_true
  simp only [rowsLenChk, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  exact hc i (by omega)

theorem LcT_pos : 0 < LcT := by
  -- kcost: one literal comparison
  decide +kernel

theorem rows_zero : Rr 0 0 = 0 := by
  -- kcost: one list lookup
  decide +kernel

theorem rows_spec {i j : ℕ} (h : i + j ≤ DM) (h1 : 1 ≤ i + j) :
    (Rr i j : ℝ) * (((i : ℝ) + j) * ((i : ℝ) + j + 1)) = LcT * ((i + j + 1).choose i : ℝ) := by
  have hc := rowsChk_true
  simp only [rowsChk, List.all_eq_true, List.mem_range] at hc
  have := hc i (by omega) j (by omega)
  have h0 : i + j ≠ 0 := by omega
  simp only [h0, if_false, beq_iff_eq] at this
  rw [← Nat.choose_eq_descFactorial_div_factorial] at this
  have := congrArg (fun z : ℤ => (z : ℝ)) this
  push_cast at this
  exact this

/-- The polynomial identity: the moment sum equals the coefficient sum. -/
theorem poly_id (S : ℕ → ℝ) (Tot Tz dl z : ℝ) (D : ℕ) (hD : D ≤ DM) (hTz : Tz ≠ 0) (hTot : Tot ≠ 0) :
    ∑ i ∈ Finset.range D, MoE S (i + 1) (dl * z / Lam) /
        (Tot * ((i : ℝ) + 2) * (((i : ℝ) + 1) * (Tz / Lam) ^ (i + 1))) =
      (1 / Tot) * ∑ m ∈ Finset.range (D + 1), (-dl * z) ^ m *
        ((∑ j ∈ Finset.range (D + 1 - m), (Rr m j : ℝ) * S j * Tz ^ (D + 1 - m - 1 - j)) /
          ((LcT : ℝ) * Tz ^ D)) := by
  have hL : (LcT : ℝ) ≠ 0 := by exact_mod_cast LcT_pos.ne'
  have hLam : (Lam : ℝ) ≠ 0 := by norm_num
  set X : ℝ := -dl * z with hX
  -- F k r
  set F : ℕ → ℕ → ℝ := fun k r => (Rr r (k - r) : ℝ) / LcT * X ^ r * S (k - r) / Tz ^ k with hF
  have step1 : ∀ i ∈ Finset.range D, MoE S (i + 1) (dl * z / Lam) /
      (Tot * ((i : ℝ) + 2) * (((i : ℝ) + 1) * (Tz / Lam) ^ (i + 1))) =
      (1 / Tot) * ∑ r ∈ Finset.range (i + 1 + 1), F (i + 1) r := by
    intro i hi
    have hiD : i + 1 ≤ D := by have := Finset.mem_range.1 hi; omega
    unfold MoE
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ i + 1 := by have := Finset.mem_range.1 hr; omega
    obtain ⟨n, hn⟩ : ∃ n, i + 1 = r + n := ⟨i + 1 - r, by omega⟩
    have e5 : i + 1 - r = n := by omega
    have hsp := rows_spec (i := r) (j := n) (by omega) (by omega)
    have hc1 : (r : ℝ) + n = (i : ℝ) + 1 := by exact_mod_cast hn.symm
    have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hi2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    rw [hc1, show (i : ℝ) + 1 + 1 = (i : ℝ) + 2 by ring] at hsp
    have hR : (Rr r n : ℝ) / LcT = ((i + 1 + 1).choose r : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
      have hn' : r + n + 1 = i + 1 + 1 := by omega
      rw [hn'] at hsp
      field_simp
      linarith
    simp only [hF]
    rw [e5, hR, hn]
    have e6 : (-(dl * z / Lam)) ^ r = X ^ r / Lam ^ r := by
      rw [hX, ← div_pow]; congr 1; ring
    rw [e6, div_pow, pow_add, pow_add]
    have hp1 : Lam ^ r ≠ 0 := pow_ne_zero _ hLam
    have hp2 : Lam ^ n ≠ 0 := pow_ne_zero _ hLam
    have hp3 : Tz ^ r ≠ 0 := pow_ne_zero _ hTz
    have hp4 : Tz ^ n ≠ 0 := pow_ne_zero _ hTz
    field_simp
  rw [Finset.sum_congr rfl step1, ← Finset.mul_sum]
  congr 1
  have h0 : ∑ r ∈ Finset.range (0 + 1), F 0 r = 0 := by
    simp [hF, rows_zero]
  have h1 : ∑ i ∈ Finset.range D, ∑ r ∈ Finset.range (i + 1 + 1), F (i + 1) r =
      ∑ k ∈ Finset.range (D + 1), ∑ r ∈ Finset.range (k + 1), F k r := by
    rw [Finset.sum_range_succ' (fun k => ∑ r ∈ Finset.range (k + 1), F k r) D, h0, add_zero]
  rw [h1]
  have h2 : ∑ k ∈ Finset.range (D + 1), ∑ r ∈ Finset.range (k + 1), F k r =
      ∑ r ∈ Finset.range (D + 1), ∑ k ∈ Finset.Ico r (D + 1), F k r := by
    have := Finset.sum_Ico_Ico_comm (M := ℝ) 0 (D + 1) (fun r k => F k r)
    simp only [Finset.range_eq_Ico]
    exact this.symm
  rw [h2]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ D := by have := Finset.mem_range.1 hm; omega
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj' => ?_
  have hj2 : j < D + 1 - m := Finset.mem_range.1 hj'
  simp only [hF]
  have e8 : m + j - m = j := by omega
  rw [e8]
  have hp : Tz ^ (m + j) ≠ 0 := pow_ne_zero _ hTz
  have hq : Tz ^ (D + 1 - m - 1 - j) ≠ 0 := pow_ne_zero _ hTz
  have e9 : Tz ^ D = Tz ^ (D + 1 - m - 1 - j) * Tz ^ (m + j) := by
    rw [← pow_add]; congr 1; omega
  rw [e9]
  field_simp

/-! ### Clusters -/

def seg (src : List Tr) (i j : ℕ) : List Tr := (src.drop i).take (j - i)

theorem seg_append (src : List Tr) {i j k : ℕ} (h1 : i ≤ j) (h2 : j ≤ k) :
    seg src i j ++ seg src j k = seg src i k := by
  unfold seg
  have e : k - i = (j - i) + (k - j) := by omega
  have e2 : src.drop j = (src.drop i).drop (j - i) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e, List.take_add, e2]

def hl (a b : ℤ) : ℕ → ℤ → ℤ → List ℤ
  | 0, _, _ => []
  | n + 1, h, bp => h :: hl a b n (a * h + bp * b) (bp * b)

theorem hl_get (a b P : ℤ) : ∀ (n j m : ℕ), m < n →
    (hl a b n (P * hj a b j) (P * b ^ j)).getD m 0 = P * hj a b (j + m)
  | 0, _, _, h => by omega
  | n + 1, j, 0, _ => by simp [hl]
  | n + 1, j, m + 1, h => by
    simp only [hl, List.getD_cons_succ]
    have e1 : a * (P * hj a b j) + P * b ^ j * b = P * hj a b (j + 1) := by
      simp only [hj, pow_succ]; ring
    have e2 : P * b ^ j * b = P * b ^ (j + 1) := by rw [pow_succ]; ring
    rw [e1, e2, hl_get a b P n (j + 1) m (by omega)]
    congr 2
    omega

theorem addL_get : ∀ (a b : List ℤ) (m : ℕ), (addL a b).getD m 0 = a.getD m 0 + b.getD m 0
  | [], b, m => by simp [addL]
  | a :: l, [], m => by simp [addL]
  | a :: l, b :: r, 0 => by simp [addL]
  | a :: l, b :: r, m + 1 => by
    simp only [addL, List.getD_cons_succ]
    exact addL_get l r m

def momS (g : ℤ) (n : ℕ) : List Tr → List ℤ
  | [] => []
  | t :: l => addL (hl (t.1 - g) (t.2.1 - g) n t.2.2 t.2.2) (momS g n l)

theorem momS_get (g : ℤ) (n : ℕ) : ∀ (l : List Tr) (m : ℕ), m < n → (momS g n l).getD m 0 = Sj l g m
  | [], m, _ => by simp [momS, Sj]
  | t :: l, m, h => by
    have h1 := hl_get (t.1 - g) (t.2.1 - g) t.2.2 n 0 m h
    simp only [hj, pow_zero, mul_one, zero_add] at h1
    simp only [momS, addL_get, h1, momS_get g n l m h]
    simp [Sj]

theorem floor_up (a b : ℤ) (hb : 0 < b) : (a : ℝ) / b ≤ ((a / b : ℤ) : ℝ) + 1 := by
  have := abs_le.1 (rnd_abs a b hb.ne')
  linarith [this.2]

theorem Sj_zero_nonneg (g : ℤ) : ∀ l : List Tr, (∀ t ∈ l, Vt t) → 0 ≤ Sj l g 0
  | [], _ => by simp [Sj]
  | t :: l, h => by
    have := Sj_zero_nonneg g l (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have h2 := (h t (by simp)).2
    simp only [Sj, hj, mul_one, List.map_cons, List.sum_cons] at this ⊢
    omega

structure Clu where
  i : ℕ
  j : ℕ
  g : ℤ
  R : ℕ
  D : ℕ
  S : List ℤ

def Clu.chk (src : List Tr) (c : Clu) : Bool :=
  (seg src c.i c.j).all (fun t => decide (t.1 < t.2.1) && decide (0 ≤ t.2.2) &&
      decide (c.g - c.R ≤ t.1) && decide (t.2.1 ≤ c.g + c.R)) &&
    (c.S == momS c.g (c.D + 1) (seg src c.i c.j)) && decide (c.S.length = c.D + 1) &&
    decide (c.D ≤ DM)

def pairOK (c : Clu) (Tz : ℤ) (dl : ℕ) : Bool :=
  decide (c.R + dl < Tz.natAbs) && decide (Tz.natAbs < 2 ^ 45) && lnOK Tz.natAbs

def cluQ (sc Tot Tz : ℤ) (dl : ℕ) (c : Clu) : List ℤ :=
  addL [(sc * c.S.getD 0 0 * lgv Tz.natAbs) / Tot]
    (qs Tz c.S (-sc * 2 ^ 64) (LcT * Tot * Tz ^ c.D) (-(dl : ℤ)) (c.D + 1) 1 rowsT)

def cluE (sc Tot Tz : ℤ) (dl : ℕ) (c : Clu) : ℤ :=
  (|sc| * c.S.getD 0 0 * 2 ^ 64 * ((c.R : ℤ) + dl) ^ (c.D + 1)) /
      (Tot * |Tz| ^ c.D * (|Tz| - c.R - dl)) + 1 +
    (|sc| * c.S.getD 0 0 * lgErr) / Tot + 1 + 1 + (c.D + 1)

theorem clu_abs {src : List Tr} {Tot sc Tz : ℤ} {dl : ℕ} {c : Clu} (hc : c.chk src = true)
    (hT : 0 < Tot) (hp : pairOK c Tz dl = true) {z : ℝ} (hz1 : |z| ≤ 1) :
    |(sc : ℝ) * potL ((seg src c.i c.j).map (mkCell 1 Tot)) (((c.g + Tz : ℤ) : ℝ) / Lam + dl * z / Lam) -
      evalZ (cluQ sc Tot Tz dl c) z / 2 ^ 64| ≤ (cluE sc Tot Tz dl c : ℝ) / 2 ^ 64 := by
  simp only [Clu.chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hall, hS⟩, hlen⟩, hD⟩ := hc
  simp only [pairOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hRP, hP45⟩, hln⟩ := hp
  set l := seg src c.i c.j with hl
  set D := c.D with hDdef
  have hV : ∀ t ∈ l, Vt t := fun t ht => ⟨(hall t ht).1.1.1, (hall t ht).1.1.2⟩
  have hTr : (0:ℝ) < Tot := by exact_mod_cast hT
  have hLam : (0:ℝ) < Lam := by norm_num
  set P := Tz.natAbs with hPdef
  have hTz0 : Tz ≠ 0 := by
    intro h; rw [hPdef, h] at hRP; simp at hRP
  have hPR : ((P : ℕ) : ℝ) = |(Tz : ℝ)| := by
    rw [hPdef, Nat.cast_natAbs]; push_cast; rfl
  have hPZ : ((P : ℕ) : ℤ) = |Tz| := by rw [hPdef]; exact Int.natCast_natAbs Tz
  have hPpos : (0:ℝ) < P := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hTzr : (Tz : ℝ) ≠ 0 := by exact_mod_cast hTz0
  set T : ℝ := (Tz : ℝ) / Lam with hTdef
  set x : ℝ := dl * z / Lam with hxdef
  set θ : ℝ := ((c.R : ℝ) + dl) / P with hθdef
  have hRPr : (c.R : ℝ) + dl < P := by exact_mod_cast hRP
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one hPpos]; exact hRPr
  have hθ0 : 0 ≤ θ := by positivity
  have hT0 : T ≠ 0 := div_ne_zero hTzr hLam.ne'
  have habsT : |T| = (P : ℝ) / Lam := by
    rw [hTdef, abs_div, abs_of_pos hLam, hPR]
  have hxabs : |x| ≤ (dl : ℝ) / Lam := by
    rw [hxdef, abs_div, abs_mul, abs_of_pos hLam, Nat.abs_cast]
    gcongr
    calc (dl : ℝ) * |z| ≤ dl * 1 := by gcongr
      _ = dl := mul_one _
  have hy : ((c.g + Tz : ℤ) : ℝ) / Lam + dl * z / Lam = (c.g : ℝ) / Lam + x + T := by
    rw [hTdef, hxdef]; push_cast; ring
  have hr : ∀ t ∈ l, ∀ u ∈ Icc ((t.1 : ℝ) / 10 ^ 12) ((t.2.1 : ℝ) / 10 ^ 12),
      |(u - ((c.g : ℝ) / Lam + x)) / T| ≤ θ := by
    intro t ht u hu
    have h1 : ((c.g : ℝ) - c.R) ≤ t.1 := by exact_mod_cast (hall t ht).1.2
    have h2 : (t.2.1 : ℝ) ≤ (c.g : ℝ) + c.R := by exact_mod_cast (hall t ht).2
    have hu1 : ((c.g : ℝ) - c.R) / Lam ≤ u := le_trans (by gcongr) hu.1
    have hu2 : u ≤ ((c.g : ℝ) + c.R) / Lam := le_trans hu.2 (by gcongr)
    have hb : |u - ((c.g : ℝ) / Lam + x)| ≤ ((c.R : ℝ) + dl) / Lam := by
      have := abs_le.1 hxabs
      rw [abs_le]
      constructor
      · have : ((c.g : ℝ) - c.R) / Lam = (c.g : ℝ) / Lam - (c.R : ℝ) / Lam := by ring
        have h3 : ((c.R : ℝ) + dl) / Lam = (c.R : ℝ) / Lam + (dl : ℝ) / Lam := by ring
        linarith [(abs_le.1 hxabs).2]
      · have : ((c.g : ℝ) + c.R) / Lam = (c.g : ℝ) / Lam + (c.R : ℝ) / Lam := by ring
        have h3 : ((c.R : ℝ) + dl) / Lam = (c.R : ℝ) / Lam + (dl : ℝ) / Lam := by ring
        linarith [(abs_le.1 hxabs).1]
    rw [abs_div, habsT, hθdef, div_le_iff₀ (by positivity)]
    calc _ ≤ ((c.R : ℝ) + dl) / Lam := hb
      _ = _ := by field_simp
  have enc := list_enc Tot c.g x T _ θ hT hT0 hy hθ1 D l hV hr
  set SR : ℕ → ℝ := fun j => (Sj l c.g j : ℝ) with hSR
  have pid := poly_id SR Tot Tz dl z D hD hTzr hTr.ne'
  set Mx : ℝ := ∑ i ∈ Finset.range D, MoE SR (i + 1) x /
        ((Tot : ℝ) * ((i : ℝ) + 2) * (((i : ℝ) + 1) * T ^ (i + 1))) with hMx
  have hSget : ∀ j, j < D + 1 → c.S.getD j 0 = Sj l c.g j := by
    intro j hj'
    rw [hS]; exact momS_get _ _ _ _ hj'
  have hS0 : c.S.getD 0 0 = Sj l c.g 0 := hSget 0 (by omega)
  have hS0n : 0 ≤ Sj l c.g 0 := Sj_zero_nonneg c.g l hV
  have hDn : LcT * Tot * Tz ^ D ≠ 0 :=
    mul_ne_zero (mul_ne_zero LcT_pos.ne' hT.ne') (pow_ne_zero _ hTz0)
  set f : ℕ → ℝ := fun m => ((-sc * 2 ^ 64 * 1 * (-(dl : ℤ)) ^ m *
      hz Tz (D + 1 - m) (rowsT.getD m []) c.S 0 : ℤ) : ℝ) / ((LcT * Tot * Tz ^ D : ℤ) : ℝ) with hf
  have qa := qs_abs Tz c.S (-sc * 2 ^ 64) (LcT * Tot * Tz ^ D) (-(dl : ℤ)) hDn hz1 (D + 1) 1 rowsT f
    ((Nat.add_le_add_right hD 1).trans rows_len) (fun m _ => rfl)
  have hfsum : ∑ m ∈ Finset.range (D + 1), f m * z ^ m = -(sc : ℝ) * 2 ^ 64 * Mx := by
    rw [pid, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m < D + 1 := Finset.mem_range.1 hm
    have hsp := hz_spec Tz (D + 1 - m) (rowsT.getD m []) c.S 0
      (le_trans (by omega) (rows_len2 (i := m) (by omega))) (by omega)
    have hcast : ((hz Tz (D + 1 - m) (rowsT.getD m []) c.S 0 : ℤ) : ℝ) =
        ∑ j ∈ Finset.range (D + 1 - m), (Rr m j : ℝ) * SR j * (Tz : ℝ) ^ (D + 1 - m - 1 - j) := by
      rw [hsp]
      push_cast
      simp only [zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j hj' => ?_
      have hj2 : j < D + 1 - m := Finset.mem_range.1 hj'
      rw [hSget j (by omega)]
      simp only [Rr, hSR]
    simp only [hf]
    push_cast
    rw [hcast] at *
    have hL : (LcT : ℝ) ≠ 0 := by exact_mod_cast LcT_pos.ne'
    have hp : (Tz : ℝ) ^ D ≠ 0 := pow_ne_zero _ hTzr
    rw [mul_pow, neg_pow (dl : ℝ) m]
    field_simp
    try ring
  have hok : P = 0 ∨ lnormOK P (10 ^ 12) = true := by
    simpa [lnOK] using hln
  have hLabs0 := lg_enc P hP45 hok
  have hLog : Real.log |T| = Real.log ((P : ℝ) / 1000000000000) := by
    rw [habsT]; norm_num [Lam]
  rw [← hLog] at hLabs0
  set L : ℝ := Real.log |T| with hLdef
  set lg : ℝ := (lgv P : ℝ) with hlg
  set S0 : ℝ := (Sj l c.g 0 : ℝ) with hS0d
  have hS0r : 0 ≤ S0 := by rw [hS0d]; exact_mod_cast hS0n
  set A := potL (l.map (mkCell 1 Tot)) (((c.g + Tz : ℤ) : ℝ) / Lam + dl * z / Lam) with hA
  have hevq : evalZ (cluQ sc Tot Tz dl c) z =
      (((sc * c.S.getD 0 0 * lgv P) / Tot : ℤ) : ℝ) +
        evalZ (qs Tz c.S (-sc * 2 ^ 64) (LcT * Tot * Tz ^ D) (-(dl : ℤ)) (D + 1) 1 rowsT) z := by
    unfold cluQ
    rw [evalZ_addL]
    simp only [evalZ, mul_zero, add_zero]
    rfl
  rw [hevq]
  set q0 : ℝ := (((sc * c.S.getD 0 0 * lgv P) / Tot : ℤ) : ℝ) with hq0
  set Eq := evalZ (qs Tz c.S (-sc * 2 ^ 64) (LcT * Tot * Tz ^ D) (-(dl : ℤ)) (D + 1) 1 rowsT) z with hEq
  rw [hfsum] at qa
  have r0 := rnd_abs (sc * c.S.getD 0 0 * lgv P) Tot hT.ne'
  rw [← hq0] at r0
  have hcast0 : ((sc * c.S.getD 0 0 * lgv P : ℤ) : ℝ) = (sc : ℝ) * S0 * lg := by
    rw [hS0]; push_cast; rfl
  rw [hcast0] at r0
  set τ : ℝ := θ ^ (D + 1) / (1 - θ) with hτ
  have hτ0 : 0 ≤ τ := by
    have : 0 < 1 - θ := by linarith
    positivity
  set sa : ℝ := |(sc : ℝ)| with hsa
  have hsa0 : 0 ≤ sa := abs_nonneg _
  have b1 : |(sc : ℝ) * (A - (S0 / Tot * L - Mx))| ≤ sa * (S0 / Tot * τ) := by
    rw [abs_mul]; gcongr
  have b2 : |(sc : ℝ) * (S0 / Tot) * (L - lg / 2 ^ 64)| ≤ sa * (S0 / Tot) * ((lgErr : ℝ) / 2 ^ 64) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ S0 / Tot)]
    gcongr
  have b3 : |((sc : ℝ) * S0 * lg / Tot - q0) / 2 ^ 64| ≤ 1 / 2 ^ 64 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2 ^ 64)]
    gcongr
  have b4 : |(-(sc : ℝ) * 2 ^ 64 * Mx - Eq) / 2 ^ 64| ≤ ((D : ℝ) + 1) / 2 ^ 64 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2 ^ 64), abs_sub_comm]
    gcongr
    simpa using qa
  have etot : (sc : ℝ) * A - (q0 + Eq) / 2 ^ 64 =
      (sc : ℝ) * (A - (S0 / Tot * L - Mx)) + (sc : ℝ) * (S0 / Tot) * (L - lg / 2 ^ 64) +
      ((sc : ℝ) * S0 * lg / Tot - q0) / 2 ^ 64 + (-(sc : ℝ) * 2 ^ 64 * Mx - Eq) / 2 ^ 64 := by
    field_simp
    ring
  rw [etot]
  have hpos1 : (0:ℝ) < (P : ℝ) - c.R - dl := by linarith
  have hb1 : 0 < Tot * |Tz| ^ D * (|Tz| - c.R - dl) := by
    have h1 : 0 < |Tz| := abs_pos.2 hTz0
    have h2 : 0 < |Tz| - c.R - dl := by
      rw [← hPZ]; have : ((c.R + dl : ℕ) : ℤ) < (P : ℤ) := by exact_mod_cast hRP
      push_cast at this; linarith
    positivity
  have f1 := floor_up (|sc| * c.S.getD 0 0 * 2 ^ 64 * ((c.R : ℤ) + dl) ^ (D + 1))
    (Tot * |Tz| ^ D * (|Tz| - c.R - dl)) hb1
  have f2 := floor_up (|sc| * c.S.getD 0 0 * lgErr) Tot hT
  have hzabs : ((|Tz| : ℤ) : ℝ) = (P : ℝ) := by rw [← hPZ]; norm_cast
  have hscabs : ((|sc| : ℤ) : ℝ) = sa := by rw [hsa]; push_cast; rfl
  have hSS : ((c.S.getD 0 0 : ℤ) : ℝ) = S0 := by rw [hS0]
  have hτ' : τ = ((c.R : ℝ) + dl) ^ (D + 1) / ((P : ℝ) ^ D * ((P : ℝ) - c.R - dl)) := by
    rw [hτ, hθdef, div_pow, pow_succ (P : ℝ) D]
    have e : 1 - ((c.R : ℝ) + dl) / P = ((P : ℝ) - c.R - dl) / P := by
      field_simp; ring
    rw [e]
    field_simp
  have e1 : ((|sc| * c.S.getD 0 0 * 2 ^ 64 * ((c.R : ℤ) + dl) ^ (D + 1) : ℤ) : ℝ) /
      ((Tot * |Tz| ^ D * (|Tz| - c.R - dl) : ℤ) : ℝ) = sa * (S0 / Tot * τ) * 2 ^ 64 := by
    rw [hτ']
    push_cast
    rw [hSS, ← hPR]
    have : (P : ℝ) ^ D ≠ 0 := by positivity
    field_simp
    rw [← hsa]
    ring
  have e2 : ((|sc| * c.S.getD 0 0 * lgErr : ℤ) : ℝ) / (Tot : ℝ) / 2 ^ 64 =
      sa * (S0 / Tot) * ((lgErr : ℝ) / 2 ^ 64) := by
    push_cast
    rw [hSS]
    field_simp
    rw [← hsa]
    ring
  rw [e1] at f1
  have f2' : sa * (S0 / Tot) * ((lgErr : ℝ) / 2 ^ 64) ≤
      ((((|sc| * c.S.getD 0 0 * lgErr) / Tot : ℤ) : ℝ) + 1) / 2 ^ 64 := by
    rw [← e2]; gcongr
  have f1' : sa * (S0 / Tot * τ) ≤
      ((((|sc| * c.S.getD 0 0 * 2 ^ 64 * ((c.R : ℤ) + dl) ^ (D + 1)) /
        (Tot * |Tz| ^ D * (|Tz| - c.R - dl)) : ℤ) : ℝ) + 1) / 2 ^ 64 := by
    rw [le_div_iff₀ (by norm_num)]; exact f1
  have hE : (cluE sc Tot Tz dl c : ℝ) / 2 ^ 64 =
      ((((|sc| * c.S.getD 0 0 * 2 ^ 64 * ((c.R : ℤ) + dl) ^ (D + 1)) /
        (Tot * |Tz| ^ D * (|Tz| - c.R - dl)) : ℤ) : ℝ) + 1) / 2 ^ 64 +
      ((((|sc| * c.S.getD 0 0 * lgErr) / Tot : ℤ) : ℝ) + 1) / 2 ^ 64 + 1 / 2 ^ 64 +
      ((D : ℝ) + 1) / 2 ^ 64 := by
    unfold cluE
    push_cast
    ring
  rw [hE]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (b1.trans f1') (b2.trans f2'))) b3)) b4)

/-! ### Rounded coefficient lists from a function -/

def rl (f : ℕ → ℤ × ℤ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | n + 1, i => ((f i).1 / (f i).2) :: rl f n (i + 1)

theorem rl_abs (f : ℕ → ℤ × ℤ) {z : ℝ} (hz : |z| ≤ 1) : ∀ (n i : ℕ), (∀ m, (f m).2 ≠ 0) →
    |evalZ (rl f n i) z - ∑ m ∈ Finset.range n, ((f (i + m)).1 : ℝ) / (f (i + m)).2 * z ^ m| ≤ n
  | 0, _, _ => by simp [rl, evalZ]
  | n + 1, i, hf => by
    have ih := rl_abs f hz n (i + 1) hf
    simp only [rl, evalZ]
    rw [Finset.sum_range_succ']
    have e : ∑ k ∈ Finset.range n, ((f (i + (k + 1))).1 : ℝ) / (f (i + (k + 1))).2 * z ^ (k + 1) =
        z * ∑ k ∈ Finset.range n, ((f (i + 1 + k)).1 : ℝ) / (f (i + 1 + k)).2 * z ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show i + (k + 1) = i + 1 + k by ring]
      ring
    rw [e]
    have r := rnd_abs (f i).1 (f i).2 (hf i)
    simp only [add_zero, pow_zero, mul_one]
    set A : ℝ := (((f i).1 / (f i).2 : ℤ) : ℝ)
    set B : ℝ := ((f i).1 : ℝ) / (f i).2
    set E := evalZ (rl f n (i + 1)) z
    set F := ∑ k ∈ Finset.range n, ((f (i + 1 + k)).1 : ℝ) / (f (i + 1 + k)).2 * z ^ k
    have e2 : A + z * E - (z * F + B) = (A - B) + z * (E - F) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h3 : |A - B| ≤ 1 := by rw [abs_sub_comm]; exact r
    have h4 : |z| * |E - F| ≤ 1 * n := by gcongr
    push_cast
    linarith

/-! ### Logarithm items -/

def Jn : ℕ := 6

def lamZ : ℤ := 10 ^ 12

/-- `(num, den)` of the coefficient of `z^(k+1)` in `c log|(Tz - d z)/Lam|`, scale `2^64`. -/
def logF (cn cd Tz d : ℤ) (k : ℕ) : ℤ × ℤ :=
  (-cn * 2 ^ 64 * d ^ (k + 1), cd * Tz ^ (k + 1) * ((k : ℤ) + 1))

def logQ (cn cd Tz d : ℤ) : List ℤ :=
  ((cn * lgv Tz.natAbs) / cd) :: rl (logF cn cd Tz d) Jn 0

def logE (cn cd Tz d : ℤ) : ℤ :=
  (cn * 2 * 2 ^ 64 * |d| ^ (Jn + 1)) / (cd * |Tz| ^ (Jn + 1)) + 1 + (cn * lgErr) / cd + 1 + 1 + Jn

def logOK (cn cd Tz d : ℤ) : Bool :=
  decide (0 ≤ cn) && decide (0 < cd) && decide (0 < Tz) && decide (2 * |d| ≤ Tz) &&
    decide (Tz.natAbs < 2 ^ 45) && lnOK Tz.natAbs

theorem log_up {cn cd Tz d : ℤ} (h : logOK cn cd Tz d = true) {z : ℝ} (hz : |z| ≤ 1) :
    (cn : ℝ) / cd * Real.log (((Tz : ℝ) - d * z) / Lam) ≤
      (evalZ (logQ cn cd Tz d) z + logE cn cd Tz d) / 2 ^ 64 := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hcn, hcd⟩, hT⟩, hd⟩, h45⟩, hln⟩ := h
  have hLam : (0:ℝ) < Lam := by norm_num
  have hTr : (0:ℝ) < Tz := by exact_mod_cast hT
  have hcdr : (0:ℝ) < cd := by exact_mod_cast hcd
  have hcnr : (0:ℝ) ≤ cn := by exact_mod_cast hcn
  have hdr : 2 * |(d : ℝ)| ≤ Tz := by exact_mod_cast hd
  set T : ℝ := (Tz : ℝ) / Lam with hTd
  set a : ℝ := (d : ℝ) / Tz with had
  set x : ℝ := a * z with hx
  have habsa : |a| ≤ 1 / 2 := by
    rw [had, abs_div, abs_of_pos hTr, div_le_iff₀ hTr]; linarith
  have hxa : |x| ≤ |a| := by
    rw [hx, abs_mul]
    calc |a| * |z| ≤ |a| * 1 := by gcongr
      _ = |a| := mul_one _
  have hT0 : T ≠ 0 := by positivity
  have hal1 : |a| < 1 := by linarith
  have hlog := logT_abs hT0 hxa hal1 Jn
  have ev : T * (1 - x) = ((Tz : ℝ) - d * z) / Lam := by
    rw [hTd, hx, had]; field_simp
  rw [ev] at hlog
  have hpos : 0 < ((Tz : ℝ) - d * z) / Lam := by
    have : (d : ℝ) * z ≤ |(d : ℝ)| := by
      calc (d : ℝ) * z ≤ |(d : ℝ) * z| := le_abs_self _
        _ = |(d:ℝ)| * |z| := abs_mul _ _
        _ ≤ |(d:ℝ)| * 1 := by gcongr
        _ = _ := mul_one _
    have h0 := abs_nonneg (d : ℝ)
    have : 0 < (Tz : ℝ) - d * z := by linarith
    positivity
  rw [abs_of_pos hpos] at hlog
  have hTabs : Real.log |T| = Real.log (((Tz.natAbs : ℕ) : ℝ) / 1000000000000) := by
    rw [abs_of_pos (by positivity : 0 < T), hTd]
    have : ((Tz.natAbs : ℕ) : ℝ) = (Tz : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast; exact abs_of_pos hTr
    rw [this]; norm_num [Lam]
  have hok : Tz.natAbs = 0 ∨ lnormOK Tz.natAbs (10 ^ 12) = true := by simpa [lnOK] using hln
  have hL := lg_enc Tz.natAbs h45 hok
  rw [← hTabs] at hL
  set Lg := Real.log (((Tz : ℝ) - d * z) / Lam) with hLg
  set L := Real.log |T| with hLd
  set lg : ℝ := (lgv Tz.natAbs : ℝ) with hlgd
  have hfne : ∀ m, (logF cn cd Tz d m).2 ≠ 0 := by
    intro m
    simp only [logF]
    have h1 : (cd : ℤ) ≠ 0 := hcd.ne'
    have h2 : Tz ^ (m + 1) ≠ 0 := pow_ne_zero _ hT.ne'
    have h3 : ((m : ℤ) + 1) ≠ 0 := by omega
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  have hrl := rl_abs (logF cn cd Tz d) hz Jn 0 hfne
  -- exact coefficient sum
  have hsum : ∑ m ∈ Finset.range Jn, (((logF cn cd Tz d (0 + m)).1 : ℝ) / (logF cn cd Tz d (0 + m)).2) * z ^ m * z =
      -(cn : ℝ) / cd * 2 ^ 64 * Pl Jn x := by
    unfold Pl
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [logF, zero_add, hx, had]
    push_cast
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have : (Tz : ℝ) ^ (m + 1) ≠ 0 := by positivity
    rw [mul_pow, div_pow]
    field_simp
    ring
  set c : ℝ := (cn : ℝ) / cd with hc
  have hc0 : 0 ≤ c := by positivity
  have hJ : ((Jn : ℕ) : ℝ) = 6 := by norm_num [Jn]
  set Rr := evalZ (rl (logF cn cd Tz d) Jn 0) z with hRr
  set Sg := ∑ m ∈ Finset.range Jn, (((logF cn cd Tz d (0 + m)).1 : ℝ) / (logF cn cd Tz d (0 + m)).2) * z ^ m with hSg
  have hzS : Sg * z = -c * 2 ^ 64 * Pl Jn x := by
    rw [hSg, Finset.sum_mul, hsum, hc]; ring
  have hzR : -(Jn : ℝ) - c * 2 ^ 64 * Pl Jn x ≤ z * Rr := by
    have h1 : |z * (Rr - Sg)| ≤ Jn := by
      rw [abs_mul]
      calc |z| * |Rr - Sg| ≤ 1 * Jn := by gcongr
        _ = _ := one_mul _
    have h2 := (abs_le.1 h1).1
    have h3 : z * Rr = z * (Rr - Sg) + Sg * z := by ring
    rw [h3, hzS]
    linarith
  have hE1 := (abs_le.1 hlog).2
  have hrl0 : |a| ^ (Jn + 1) / (1 - |a|) ≤ 2 * |a| ^ (Jn + 1) := by
    have h1 : 0 < 1 - |a| := by linarith
    rw [div_le_iff₀ h1]
    have h2 : 0 ≤ |a| ^ (Jn + 1) := by positivity
    nlinarith
  have q0r := rnd_abs (cn * lgv Tz.natAbs) cd hcd.ne'
  have q0' : c * lg ≤ (((cn * lgv Tz.natAbs) / cd : ℤ) : ℝ) + 1 := by
    have := (abs_le.1 q0r).2
    have e : ((cn * lgv Tz.natAbs : ℤ) : ℝ) / cd = c * lg := by
      push_cast; rw [hc, hlgd]; ring
    rw [e] at this
    linarith
  have hLu : L ≤ lg / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64 := by
    have := (abs_le.1 hL).2
    linarith
  have ft := floor_up (cn * 2 * 2 ^ 64 * |d| ^ (Jn + 1)) (cd * |Tz| ^ (Jn + 1)) (by positivity)
  have fl := floor_up (cn * lgErr) cd hcd
  have et : ((cn * 2 * 2 ^ 64 * |d| ^ (Jn + 1) : ℤ) : ℝ) / ((cd * |Tz| ^ (Jn + 1) : ℤ) : ℝ) =
      c * 2 * 2 ^ 64 * |a| ^ (Jn + 1) := by
    rw [had, abs_div, abs_of_pos hTr, hc, div_pow]
    push_cast
    rw [abs_of_pos hTr]
    field_simp
    norm_num
  have el : ((cn * lgErr : ℤ) : ℝ) / (cd : ℝ) = c * lgErr := by
    push_cast; rw [hc]; ring
  rw [et] at ft
  rw [el] at fl
  have hev : evalZ (logQ cn cd Tz d) z = (((cn * lgv Tz.natAbs) / cd : ℤ) : ℝ) + z * Rr := rfl
  rw [hev, le_div_iff₀ (by norm_num)]
  have hEv : (logE cn cd Tz d : ℝ) = (((cn * 2 * 2 ^ 64 * |d| ^ (Jn + 1)) / (cd * |Tz| ^ (Jn + 1)) : ℤ) : ℝ) + 1 +
      (((cn * lgErr) / cd : ℤ) : ℝ) + 1 + 1 + Jn := by
    unfold logE; push_cast; ring
  rw [hEv]
  have key : c * Lg ≤ c * (L - Pl Jn x) + c * (2 * |a| ^ (Jn + 1)) := by
    rw [← mul_add]
    gcongr
    linarith
  have k2 : c * L ≤ c * (lg / 2 ^ 64) + c * ((lgErr : ℝ) / 2 ^ 64) := by
    rw [← mul_add]; gcongr
  have e3 : c * Lg * 2 ^ 64 ≤ c * lg + c * lgErr - c * 2 ^ 64 * Pl Jn x + c * 2 * 2 ^ 64 * |a| ^ (Jn + 1) := by
    have := mul_le_mul_of_nonneg_right (key.trans (by linarith [k2] : c * (L - Pl Jn x) + c * (2 * |a| ^ (Jn + 1)) ≤
      c * (lg / 2 ^ 64) + c * ((lgErr : ℝ) / 2 ^ 64) - c * Pl Jn x + c * (2 * |a| ^ (Jn + 1)))) (by norm_num : (0:ℝ) ≤ 2 ^ 64)
    calc _ ≤ _ := this
      _ = _ := by field_simp
  linarith

/-- Monotone logarithm item (end ranges). -/
def monoQ (cn cd B : ℤ) : List ℤ := [(cn * lgv B.natAbs) / cd]
def monoE (cn cd : ℤ) : ℤ := (cn * lgErr) / cd + 1 + 1

def monoOK (cn cd B : ℤ) : Bool :=
  decide (0 ≤ cn) && decide (0 < cd) && decide (0 < B) && decide (B.natAbs < 2 ^ 45) && lnOK B.natAbs

theorem mono_up {cn cd B : ℤ} (h : monoOK cn cd B = true) {u : ℝ} (hu : 0 < u) (huB : u ≤ (B : ℝ) / Lam) :
    (cn : ℝ) / cd * Real.log u ≤ (evalZ (monoQ cn cd B) 0 + monoE cn cd) / 2 ^ 64 := by
  simp only [monoOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hcn, hcd⟩, hB⟩, h45⟩, hln⟩ := h
  have hcdr : (0:ℝ) < cd := by exact_mod_cast hcd
  have hcnr : (0:ℝ) ≤ cn := by exact_mod_cast hcn
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hok : B.natAbs = 0 ∨ lnormOK B.natAbs (10 ^ 12) = true := by simpa [lnOK] using hln
  have hL := lg_enc B.natAbs h45 hok
  have hcast : ((B.natAbs : ℕ) : ℝ) = (B : ℝ) := by
    rw [Nat.cast_natAbs]; push_cast; exact abs_of_pos hBr
  rw [hcast] at hL
  set lg : ℝ := (lgv B.natAbs : ℝ) with hlg
  have h1 : Real.log u ≤ Real.log ((B : ℝ) / 1000000000000) := by
    apply Real.log_le_log hu
    have e : (Lam : ℝ) = 1000000000000 := by norm_num [Lam]
    rw [e] at huB
    exact huB
  have h2 := (abs_le.1 hL).2
  set c : ℝ := (cn : ℝ) / cd with hc
  have hc0 : 0 ≤ c := by positivity
  have h3 : Real.log u ≤ lg / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64 := by linarith
  have q := (abs_le.1 (rnd_abs (cn * lgv B.natAbs) cd hcd.ne')).2
  have e : ((cn * lgv B.natAbs : ℤ) : ℝ) / cd = c * lg := by
    push_cast; rw [hc, hlg]; ring
  rw [e] at q
  have fl := floor_up (cn * lgErr) cd hcd
  have el : ((cn * lgErr : ℤ) : ℝ) / (cd : ℝ) = c * lgErr := by
    push_cast; rw [hc]; ring
  rw [el] at fl
  have hev : evalZ (monoQ cn cd B) 0 = (((cn * lgv B.natAbs) / cd : ℤ) : ℝ) := by
    simp [monoQ, evalZ]
  have hE : (monoE cn cd : ℝ) = (((cn * lgErr) / cd : ℤ) : ℝ) + 1 + 1 := by
    unfold monoE; push_cast; ring
  rw [hev, hE, le_div_iff₀ (by norm_num)]
  have h4 : c * Real.log u ≤ c * (lg / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64) := by gcongr
  have h5 := mul_le_mul_of_nonneg_right h4 (by norm_num : (0:ℝ) ≤ 2 ^ 64)
  have h6 : c * (lg / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64) * 2 ^ 64 = c * lg + c * lgErr := by
    field_simp
  linarith

/-! ### Node items -/

noncomputable def ph (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ (i + 2) / (((i : ℝ) + 2) * ((i : ℝ) + 1))

theorem ph_id (x : ℝ) : ∀ J : ℕ, x + (1 - x) * (-Pl (J + 1) x) =
    ph J x + x ^ (J + 2) / ((J : ℝ) + 1)
  | 0 => by simp [Pl, ph]; ring
  | J + 1 => by
    have ih := ph_id x J
    have h1 : Pl (J + 1 + 1) x = Pl (J + 1) x + x ^ (J + 2) / ((J : ℝ) + 2) := by
      unfold Pl
      rw [Finset.sum_range_succ]
      congr 2
      push_cast; ring
    have h2 : ph (J + 1) x = ph J x + x ^ (J + 2) / (((J : ℝ) + 2) * ((J : ℝ) + 1)) := by
      unfold ph
      rw [Finset.sum_range_succ]
    rw [h1, h2]
    have e : x + (1 - x) * -(Pl (J + 1) x + x ^ (J + 2) / ((J : ℝ) + 2)) =
        (x + (1 - x) * -Pl (J + 1) x) - (1 - x) * (x ^ (J + 2) / ((J : ℝ) + 2)) := by ring
    rw [e, ih]
    have a1 : (J : ℝ) + 1 ≠ 0 := by positivity
    have a2 : (J : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    rw [show J + 1 + 2 = (J + 2) + 1 by ring, pow_succ x (J + 2)]
    field_simp
    ring

def nodeF (n d Tz : ℤ) (δ : ℕ) (k : ℕ) : ℤ × ℤ :=
  (n * 2 ^ 64 * (δ : ℤ) ^ (k + 2), d * lamZ * Tz ^ (k + 1) * ((k : ℤ) + 2) * ((k : ℤ) + 1))

def nodeQ (n d Tz : ℤ) (δ : ℕ) : List ℤ :=
  ((n * Tz * (lgv Tz.natAbs - 2 ^ 64)) / (d * lamZ)) ::
    ((-n * δ * lgv Tz.natAbs) / (d * lamZ)) :: rl (nodeF n d Tz δ) 5 0

def nodeE (n d Tz : ℤ) (δ : ℕ) : ℤ :=
  (|n| * |Tz| * 3 * lgErr) / (2 * d * lamZ) + 1 +
    (|n| * 4 * 2 ^ 64 * (δ : ℤ) ^ (Jn + 1)) / (d * lamZ * |Tz| ^ Jn) + 1 + 1 + 1 + 5

def nodeOK (d Tz : ℤ) (δ : ℕ) : Bool :=
  decide (0 < d) && decide (2 * (δ : ℤ) ≤ |Tz|) && decide (Tz ≠ 0) &&
    decide (Tz.natAbs < 2 ^ 45) && lnOK Tz.natAbs

set_option maxHeartbeats 1600000 in
theorem node_up {n d Tz : ℤ} {δ : ℕ} (h : nodeOK d Tz δ = true) {z : ℝ} (hz : |z| ≤ 1) :
    (n : ℝ) / d * Fv (((Tz : ℝ) - δ * z) / Lam) ≤
      (evalZ (nodeQ n d Tz δ) z + nodeE n d Tz δ) / 2 ^ 64 := by
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hd, hδ⟩, hT0⟩, h45⟩, hln⟩ := h
  have hLam : (0:ℝ) < Lam := by norm_num
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hTr : (Tz : ℝ) ≠ 0 := by exact_mod_cast hT0
  have hTabs : (0:ℝ) < |(Tz : ℝ)| := abs_pos.2 hTr
  have hδr : 2 * (δ : ℝ) ≤ |(Tz : ℝ)| := by exact_mod_cast hδ
  set T : ℝ := (Tz : ℝ) / Lam with hTd
  set a : ℝ := (δ : ℝ) / Tz with had
  set x : ℝ := a * z with hx
  have habsa : |a| ≤ 1 / 2 := by
    rw [had, abs_div, Nat.abs_cast, div_le_iff₀ hTabs]; linarith
  have hxa : |x| ≤ |a| := by
    rw [hx, abs_mul]
    calc |a| * |z| ≤ |a| * 1 := by gcongr
      _ = |a| := mul_one _
  have hT0' : T ≠ 0 := div_ne_zero hTr hLam.ne'
  have hal1 : |a| < 1 := by linarith
  have hlog := logT_abs hT0' hxa hal1 Jn
  have ev : T * (1 - x) = ((Tz : ℝ) - δ * z) / Lam := by
    rw [hTd, hx, had]; field_simp
  rw [ev] at hlog
  set v : ℝ := ((Tz : ℝ) - δ * z) / Lam with hv
  have hTn : |T| = (((Tz.natAbs : ℕ) : ℝ)) / 1000000000000 := by
    rw [hTd, abs_div, abs_of_pos hLam, Nat.cast_natAbs]; push_cast; norm_num [Lam]
  have hok : Tz.natAbs = 0 ∨ lnormOK Tz.natAbs (10 ^ 12) = true := by simpa [lnOK] using hln
  have hL := lg_enc Tz.natAbs h45 hok
  rw [← hTn] at hL
  set L := Real.log |T| with hLd
  set lg : ℝ := (lgv Tz.natAbs : ℝ) with hlgd
  set E0 := Real.log |v| - (L - Pl Jn x) with hE0
  have hph := ph_id x 5
  have hFv : Fv v = T * ((L - 1) - x * L + ph 5 x + x ^ 7 / 6 + (1 - x) * E0) := by
    unfold Fv
    have e1 : Real.log v = L - Pl Jn x + E0 := by
      rw [hE0, ← Real.log_abs v]; ring
    have e2 : v = T * (1 - x) := ev.symm
    rw [e1, e2]
    norm_num at hph
    have hJ6 : Pl Jn x = Pl 6 x := rfl
    rw [hJ6]
    linear_combination T * hph
  set Wn : ℝ := (n : ℝ) / d with hWn
  set Wt : ℝ := Wn * T with hWt
  have hLam2 : ((lamZ : ℤ) : ℝ) = Lam := by norm_num [lamZ, Lam]
  have hdL : d * lamZ ≠ 0 := mul_ne_zero hd.ne' (by norm_num [lamZ])
  have hdLr : (0:ℝ) < (d : ℝ) * Lam := by positivity
  have c0 : ((n * Tz * (lgv Tz.natAbs - 2 ^ 64) : ℤ) : ℝ) / ((d * lamZ : ℤ) : ℝ) = Wt * (lg - 2 ^ 64) := by
    push_cast; rw [hLam2, hWt, hWn, hTd, hlgd]; field_simp; norm_num
  have c1 : ((-n * δ * lgv Tz.natAbs : ℤ) : ℝ) / ((d * lamZ : ℤ) : ℝ) = -(Wt * a * lg) := by
    push_cast; rw [hLam2, hWt, hWn, hTd, hlgd, had]; field_simp
  have r0 := rnd_abs (n * Tz * (lgv Tz.natAbs - 2 ^ 64)) (d * lamZ) hdL
  have r1 := rnd_abs (-n * δ * lgv Tz.natAbs) (d * lamZ) hdL
  rw [c0] at r0
  rw [c1] at r1
  set q0 : ℝ := (((n * Tz * (lgv Tz.natAbs - 2 ^ 64)) / (d * lamZ) : ℤ) : ℝ) with hq0
  set q1 : ℝ := (((-n * δ * lgv Tz.natAbs) / (d * lamZ) : ℤ) : ℝ) with hq1
  have hfne : ∀ m, (nodeF n d Tz δ m).2 ≠ 0 := by
    intro m
    simp only [nodeF]
    have h3 : ((m : ℤ) + 2) ≠ 0 := by omega
    have h4 : ((m : ℤ) + 1) ≠ 0 := by omega
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hdL (pow_ne_zero _ hT0)) h3) h4
  have hrl := rl_abs (nodeF n d Tz δ) hz 5 0 hfne
  set Rr := evalZ (rl (nodeF n d Tz δ) 5 0) z with hRr
  set Sg := ∑ m ∈ Finset.range 5, (((nodeF n d Tz δ (0 + m)).1 : ℝ) / (nodeF n d Tz δ (0 + m)).2) * z ^ m with hSg
  have hzS : z * z * Sg = 2 ^ 64 * Wt * ph 5 x := by
    rw [hSg]
    unfold ph
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [nodeF, zero_add, hx, had, hWt, hWn, hTd]
    push_cast
    rw [hLam2, mul_pow, div_pow]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    have : (m : ℝ) + 2 ≠ 0 := by positivity
    have : (Tz : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hTr
    have : (Tz : ℝ) ^ (m + 2) ≠ 0 := pow_ne_zero _ hTr
    rw [pow_succ (Tz : ℝ) (m + 1)]
    field_simp
    ring
  have hzz : z * z ≤ 1 := by nlinarith [abs_le.1 hz, sq_abs z]
  have hzz0 : 0 ≤ z * z := mul_self_nonneg z
  have b2 : z * z * Sg - 5 ≤ z * z * Rr := by
    have h1 : |z * z * (Rr - Sg)| ≤ 5 := by
      rw [abs_mul, abs_of_nonneg hzz0]
      calc z * z * |Rr - Sg| ≤ 1 * 5 := by
            apply mul_le_mul hzz (by simpa using hrl) (abs_nonneg _) (by norm_num)
        _ = 5 := by norm_num
    have := (abs_le.1 h1).1
    have e : z * z * (Rr - Sg) = z * z * Rr - z * z * Sg := by ring
    rw [e] at this
    linarith
  have b1 : z * q1 ≥ -(Wt * x * lg) - 1 := by
    have h1 : |z * (q1 - -(Wt * a * lg))| ≤ 1 := by
      rw [abs_mul]
      calc |z| * |q1 - -(Wt * a * lg)| ≤ 1 * 1 := by
            apply mul_le_mul hz (by rw [abs_sub_comm]; exact r1) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have := (abs_le.1 h1).1
    have e : z * (q1 - -(Wt * a * lg)) = z * q1 + Wt * x * lg := by rw [hx]; ring
    rw [e] at this
    linarith
  have b0 : q0 ≥ Wt * (lg - 2 ^ 64) - 1 := by
    have := (abs_le.1 r0).2
    linarith
  have hx1 : |1 - x| ≤ 3 / 2 := by
    have := abs_le.1 (hxa.trans habsa)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  set A7 : ℝ := |a| ^ 7 with hA7
  have hA70 : 0 ≤ A7 := by positivity
  have hR1 : |(L - lg / 2 ^ 64) * (1 - x)| ≤ (lgErr : ℝ) / 2 ^ 64 * (3 / 2) := by
    rw [abs_mul]
    apply mul_le_mul hL hx1 (abs_nonneg _) (by positivity)
  have hE0b : |E0| ≤ 2 * A7 := by
    refine hlog.trans ?_
    have h1 : 0 < 1 - |a| := by linarith
    rw [div_le_iff₀ h1]
    have hJ : Jn + 1 = 7 := rfl
    rw [hJ]
    have h5 : A7 * (1 / 2) ≤ A7 * (1 - |a|) := mul_le_mul_of_nonneg_left (by linarith) hA70
    linarith
  have hx7 : |x ^ 7 / 6| ≤ A7 := by
    rw [abs_div, abs_pow]
    have : |x| ^ 7 ≤ A7 := by rw [hA7]; gcongr
    have h6 : |(6:ℝ)| = 6 := by norm_num
    rw [h6]
    have : 0 ≤ |x| ^ 7 := by positivity
    linarith
  have hR2 : |x ^ 7 / 6 + (1 - x) * E0| ≤ 4 * A7 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hx1 hE0b (abs_nonneg _) (by norm_num)
    linarith
  have hsum : Wn * Fv v * 2 ^ 64 = Wt * (lg - 2 ^ 64) - Wt * x * lg + 2 ^ 64 * Wt * ph 5 x +
      Wt * 2 ^ 64 * ((L - lg / 2 ^ 64) * (1 - x) + (x ^ 7 / 6 + (1 - x) * E0)) := by
    rw [hFv, hWt]
    field_simp
    ring
  set Wa : ℝ := |Wt| with hWa
  have hWa0 : 0 ≤ Wa := abs_nonneg _
  have hup : Wt * 2 ^ 64 * ((L - lg / 2 ^ 64) * (1 - x) + (x ^ 7 / 6 + (1 - x) * E0)) ≤
      Wa * (3 / 2) * lgErr + Wa * 4 * 2 ^ 64 * A7 := by
    have h1 : |Wt * 2 ^ 64 * ((L - lg / 2 ^ 64) * (1 - x) + (x ^ 7 / 6 + (1 - x) * E0))| ≤
        Wa * 2 ^ 64 * ((lgErr : ℝ) / 2 ^ 64 * (3 / 2) + 4 * A7) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2 ^ 64)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_add_le _ _).trans (add_le_add hR1 hR2)
    have h2 := (abs_le.1 h1).2
    have h3 : Wa * 2 ^ 64 * ((lgErr : ℝ) / 2 ^ 64 * (3 / 2) + 4 * A7) =
        Wa * (3 / 2) * lgErr + Wa * 4 * 2 ^ 64 * A7 := by field_simp
    linarith
  have hlam0 : 0 < lamZ := by norm_num [lamZ]
  have hb1p : 0 < 2 * d * lamZ := by positivity
  have hb2p : 0 < d * lamZ * |Tz| ^ Jn := by
    have : 0 < |Tz| := abs_pos.2 hT0
    positivity
  have f1 := floor_up (|n| * |Tz| * 3 * lgErr) (2 * d * lamZ) hb1p
  have f2 := floor_up (|n| * 4 * 2 ^ 64 * (δ : ℤ) ^ (Jn + 1)) (d * lamZ * |Tz| ^ Jn) hb2p
  have hWaE : Wa = |(n : ℝ)| / d * (|(Tz : ℝ)| / Lam) := by
    rw [hWa, hWt, hWn, hTd, abs_mul, abs_div, abs_div, abs_of_pos hdr, abs_of_pos hLam]
  have g1 : ((|n| * |Tz| * 3 * lgErr : ℤ) : ℝ) / ((2 * d * lamZ : ℤ) : ℝ) = Wa * (3 / 2) * lgErr := by
    rw [hWaE]; push_cast; rw [hLam2]; field_simp
  have g2 : ((|n| * 4 * 2 ^ 64 * (δ : ℤ) ^ (Jn + 1) : ℤ) : ℝ) / ((d * lamZ * |Tz| ^ Jn : ℤ) : ℝ) =
      Wa * 4 * 2 ^ 64 * A7 := by
    rw [hWaE, hA7, had, abs_div, Nat.abs_cast, div_pow]
    have hJ : Jn + 1 = 7 := rfl
    have hJ2 : Jn = 6 := rfl
    rw [hJ, hJ2]
    push_cast
    rw [hLam2]
    rw [pow_succ |(Tz : ℝ)| 6]
    field_simp
    norm_num
    ring
  rw [g1] at f1
  rw [g2] at f2
  have hev : evalZ (nodeQ n d Tz δ) z = q0 + z * (q1 + z * Rr) := rfl
  have hEv : (nodeE n d Tz δ : ℝ) = (((|n| * |Tz| * 3 * lgErr) / (2 * d * lamZ) : ℤ) : ℝ) + 1 +
      (((|n| * 4 * 2 ^ 64 * (δ : ℤ) ^ (Jn + 1)) / (d * lamZ * |Tz| ^ Jn) : ℤ) : ℝ) + 1 + 1 + 1 + 5 := by
    unfold nodeE; push_cast; norm_num
  rw [hev, hEv, le_div_iff₀ (by norm_num), hsum]
  have e5 : q0 + z * (q1 + z * Rr) = q0 + z * q1 + z * z * Rr := by ring
  rw [e5]
  rw [hzS] at b2
  linarith

/-! ### Inner nodes -/

theorem neg_u_log_le {u : ℝ} (h0 : 0 < u) : u * (-Real.log u) ≤ 2 / 5 := by
  have h1 := Real.add_one_le_exp (-Real.log u - 1)
  have h2 : Real.exp (-Real.log u - 1) = u⁻¹ * (Real.exp 1)⁻¹ := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log h0, div_eq_mul_inv]
  rw [h2] at h1
  have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1) (by norm_num)
    norm_num at this
    linarith
  have h3 : (Real.exp 1)⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  have h4 : u * (-Real.log u) ≤ u * (u⁻¹ * (Real.exp 1)⁻¹) := by
    apply mul_le_mul_of_nonneg_left _ h0.le
    linarith
  have h5 : u * (u⁻¹ * (Real.exp 1)⁻¹) = (Real.exp 1)⁻¹ := by
    field_simp
  linarith

theorem vlog_bounds {v b : ℝ} (hb : 0 < b) (hv : |v| ≤ b) :
    |v * (Real.log v - Real.log b)| ≤ 2 / 5 * b ∧ (0 ≤ v → v * (Real.log v - Real.log b) ≤ 0) ∧
      (v ≤ 0 → 0 ≤ v * (Real.log v - Real.log b)) := by
  by_cases h0 : v = 0
  · subst h0
    simp
    positivity
  have hav : 0 < |v| := abs_pos.2 h0
  have hl : Real.log v - Real.log b ≤ 0 := by
    rw [← Real.log_abs v]
    have := Real.log_le_log hav hv
    linarith
  refine ⟨?_, fun h => mul_nonpos_of_nonneg_of_nonpos h hl, fun h => mul_nonneg_of_nonpos_of_nonpos h hl⟩
  set u := |v| / b with hu
  have hu0 : 0 < u := by positivity
  have e : Real.log v - Real.log b = Real.log u := by
    rw [hu, Real.log_div hav.ne' hb.ne', Real.log_abs]
  have hlu : Real.log u ≤ 0 := by rw [← e]; exact hl
  rw [e, abs_mul, abs_of_nonpos hlu]
  have h1 := neg_u_log_le hu0
  have e2 : |v| * -Real.log u = b * (u * -Real.log u) := by
    rw [hu]; field_simp
  rw [e2]
  nlinarith

def innB (Tz : ℤ) (δ : ℕ) : ℤ := |Tz| + δ

def innQ (n d Tz : ℤ) (δ : ℕ) : List ℤ :=
  [(n * Tz * (lgv (innB Tz δ).natAbs - 2 ^ 64)) / (d * lamZ),
    (-n * δ * (lgv (innB Tz δ).natAbs - 2 ^ 64)) / (d * lamZ)]

def innFav (n Tz : ℤ) (δ : ℕ) : Bool :=
  (decide (0 ≤ n) && decide ((δ : ℤ) ≤ Tz)) || (decide (n ≤ 0) && decide (Tz ≤ -(δ : ℤ)))

def innE (n d Tz : ℤ) (δ : ℕ) : ℤ :=
  (|n| * innB Tz δ * lgErr) / (d * lamZ) + 1 + 1 + 1 +
    (if innFav n Tz δ then 0 else (|n| * innB Tz δ * 2 * 2 ^ 64) / (5 * d * lamZ) + 1)

def innOK (d Tz : ℤ) (δ : ℕ) : Bool :=
  decide (0 < d) && decide (0 < innB Tz δ) && decide ((innB Tz δ).natAbs < 2 ^ 45) &&
    lnOK (innB Tz δ).natAbs

set_option maxHeartbeats 800000 in
theorem inn_up {n d Tz : ℤ} {δ : ℕ} (h : innOK d Tz δ = true) {z : ℝ} (hz : |z| ≤ 1) :
    (n : ℝ) / d * Fv (((Tz : ℝ) - δ * z) / Lam) ≤
      (evalZ (innQ n d Tz δ) z + innE n d Tz δ) / 2 ^ 64 := by
  simp only [innOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hd, hB⟩, h45⟩, hln⟩ := h
  have hLam : (0:ℝ) < Lam := by norm_num
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  set B := innB Tz δ with hBd
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hBc : (B : ℝ) = |(Tz : ℝ)| + δ := by rw [hBd]; simp [innB]
  set v : ℝ := ((Tz : ℝ) - δ * z) / Lam with hv
  set b : ℝ := (B : ℝ) / Lam with hbd
  have hb : 0 < b := by positivity
  have hvb : |v| ≤ b := by
    rw [hv, hbd, abs_div, abs_of_pos hLam]
    gcongr
    rw [hBc]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, Nat.abs_cast]
    gcongr
    calc (δ : ℝ) * |z| ≤ δ * 1 := by gcongr
      _ = δ := mul_one _
  obtain ⟨g1, g2, g3⟩ := vlog_bounds hb hvb
  have hok : B.natAbs = 0 ∨ lnormOK B.natAbs (10 ^ 12) = true := by simpa [lnOK] using hln
  have hL := lg_enc B.natAbs h45 hok
  have hcast : ((B.natAbs : ℕ) : ℝ) = (B : ℝ) := by
    rw [Nat.cast_natAbs]; push_cast; exact abs_of_pos hBr
  have hbn : (B : ℝ) / 1000000000000 = b := by rw [hbd]; norm_num [Lam]
  rw [hcast, hbn] at hL
  set Lg := Real.log b with hLg
  set lg : ℝ := (lgv B.natAbs : ℝ) with hlg
  set W : ℝ := (n : ℝ) / d with hW
  set G := v * (Real.log v - Lg) with hG
  have hFv : Fv v = v * (lg / 2 ^ 64 - 1) + v * (Lg - lg / 2 ^ 64) + G := by
    unfold Fv; rw [hG]; ring
  have hLam2 : ((lamZ : ℤ) : ℝ) = Lam := by norm_num [lamZ, Lam]
  have hlam0 : 0 < lamZ := by norm_num [lamZ]
  have hdL : d * lamZ ≠ 0 := mul_ne_zero hd.ne' hlam0.ne'
  have c0 : ((n * Tz * (lgv B.natAbs - 2 ^ 64) : ℤ) : ℝ) / ((d * lamZ : ℤ) : ℝ) =
      W * (Tz : ℝ) / Lam * (lg - 2 ^ 64) := by
    push_cast; rw [hLam2, hW, hlg]; field_simp; norm_num
  have c1 : ((-n * δ * (lgv B.natAbs - 2 ^ 64) : ℤ) : ℝ) / ((d * lamZ : ℤ) : ℝ) =
      -(W * (δ : ℝ) / Lam * (lg - 2 ^ 64)) := by
    push_cast; rw [hLam2, hW, hlg]; field_simp; norm_num
  have r0 := rnd_abs (n * Tz * (lgv B.natAbs - 2 ^ 64)) (d * lamZ) hdL
  have r1 := rnd_abs (-n * δ * (lgv B.natAbs - 2 ^ 64)) (d * lamZ) hdL
  rw [c0] at r0
  rw [c1] at r1
  set q0 : ℝ := (((n * Tz * (lgv B.natAbs - 2 ^ 64)) / (d * lamZ) : ℤ) : ℝ) with hq0
  set q1 : ℝ := (((-n * δ * (lgv B.natAbs - 2 ^ 64)) / (d * lamZ) : ℤ) : ℝ) with hq1
  have hev : evalZ (innQ n d Tz δ) z = q0 + z * (q1 + z * 0) := rfl
  have b0 := (abs_le.1 r0).2
  have b1 : z * q1 ≥ z * (-(W * (δ : ℝ) / Lam * (lg - 2 ^ 64))) - 1 := by
    have h1 : |z * (q1 - -(W * (δ : ℝ) / Lam * (lg - 2 ^ 64)))| ≤ 1 := by
      rw [abs_mul]
      calc |z| * |q1 - -(W * (δ : ℝ) / Lam * (lg - 2 ^ 64))| ≤ 1 * 1 := by
            apply mul_le_mul hz (by rw [abs_sub_comm]; exact r1) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have := (abs_le.1 h1).1
    have e : z * (q1 - -(W * (δ : ℝ) / Lam * (lg - 2 ^ 64))) =
        z * q1 - z * (-(W * (δ : ℝ) / Lam * (lg - 2 ^ 64))) := by ring
    rw [e] at this
    linarith
  set Wa : ℝ := |W| with hWa
  have hWa0 : 0 ≤ Wa := abs_nonneg _
  have hWaE : Wa = |(n : ℝ)| / d := by rw [hWa, hW, abs_div, abs_of_pos hdr]
  have hP1 : W * (v * (Lg - lg / 2 ^ 64)) * 2 ^ 64 ≤ Wa * b * lgErr := by
    have h1 : |W * (v * (Lg - lg / 2 ^ 64))| ≤ Wa * (b * ((lgErr : ℝ) / 2 ^ 64)) := by
      rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ hWa0
      exact mul_le_mul hvb hL (abs_nonneg _) hb.le
    have h2 := (abs_le.1 h1).2
    have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num : (0:ℝ) ≤ 2 ^ 64)
    have h4 : Wa * (b * ((lgErr : ℝ) / 2 ^ 64)) * 2 ^ 64 = Wa * b * lgErr := by field_simp
    linarith
  have hb1p : 0 < d * lamZ := by positivity
  have f1 := floor_up (|n| * B * lgErr) (d * lamZ) hb1p
  have g1' : ((|n| * B * lgErr : ℤ) : ℝ) / ((d * lamZ : ℤ) : ℝ) = Wa * b * lgErr := by
    rw [hWaE, hbd]; push_cast; rw [hLam2]; field_simp
  rw [g1'] at f1
  have hdev : W * G * 2 ^ 64 ≤
      ((if innFav n Tz δ then 0 else (|n| * B * 2 * 2 ^ 64) / (5 * d * lamZ) + 1 : ℤ) : ℝ) := by
    by_cases hf : innFav n Tz δ = true
    · rw [if_pos hf]
      simp only [innFav, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
      have hWG : W * G ≤ 0 := by
        rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hn : 0 ≤ W := div_nonneg (by exact_mod_cast h1) hdr.le
          have hv0 : 0 ≤ v := by
            have h2r : (δ : ℝ) ≤ Tz := by exact_mod_cast h2
            have : (δ : ℝ) * z ≤ δ := by
              calc (δ : ℝ) * z ≤ δ * 1 := by
                    apply mul_le_mul_of_nonneg_left (le_trans (le_abs_self z) hz) (by positivity)
                _ = δ := mul_one _
            rw [hv]; apply div_nonneg _ hLam.le; linarith
          exact mul_nonpos_of_nonneg_of_nonpos hn (g2 hv0)
        · have hn : W ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) hdr.le
          have hv0 : v ≤ 0 := by
            have h2r : (Tz : ℝ) ≤ -(δ : ℝ) := by exact_mod_cast h2
            have : -(δ : ℝ) ≤ (δ : ℝ) * z := by
              have := (abs_le.1 hz).1
              have hδ : (0:ℝ) ≤ δ := by positivity
              nlinarith
            rw [hv]; apply div_nonpos_of_nonpos_of_nonneg _ hLam.le; linarith
          exact mul_nonpos_of_nonpos_of_nonneg hn (g3 hv0)
      push_cast
      nlinarith
    · rw [if_neg hf]
      have hp : 0 < 5 * d * lamZ := by positivity
      have f2 := floor_up (|n| * B * 2 * 2 ^ 64) (5 * d * lamZ) hp
      have g2' : ((|n| * B * 2 * 2 ^ 64 : ℤ) : ℝ) / ((5 * d * lamZ : ℤ) : ℝ) = Wa * (2 / 5 * b) * 2 ^ 64 := by
        rw [hWaE, hbd]; push_cast; rw [hLam2]; field_simp; norm_num
      rw [g2'] at f2
      have h1 : W * G ≤ Wa * (2 / 5 * b) := by
        calc W * G ≤ |W * G| := le_abs_self _
          _ = Wa * |G| := abs_mul _ _
          _ ≤ _ := by gcongr
      push_cast
      have := mul_le_mul_of_nonneg_right h1 (by norm_num : (0:ℝ) ≤ 2 ^ 64)
      linarith
  have hEv : (innE n d Tz δ : ℝ) = (((|n| * B * lgErr) / (d * lamZ) : ℤ) : ℝ) + 1 + 1 + 1 +
      ((if innFav n Tz δ then 0 else (|n| * B * 2 * 2 ^ 64) / (5 * d * lamZ) + 1 : ℤ) : ℝ) := by
    unfold innE; push_cast; ring
  have hmain : W * Fv v * 2 ^ 64 = W * (Tz : ℝ) / Lam * (lg - 2 ^ 64) +
      z * (-(W * (δ : ℝ) / Lam * (lg - 2 ^ 64))) + W * (v * (Lg - lg / 2 ^ 64)) * 2 ^ 64 + W * G * 2 ^ 64 := by
    rw [hFv]
    have e : v * (lg / 2 ^ 64 - 1) = ((Tz : ℝ) - δ * z) / Lam * (lg / 2 ^ 64 - 1) := by rw [hv]
    rw [mul_add, mul_add, e]
    field_simp
    ring
  rw [hev, hEv, le_div_iff₀ (by norm_num), hmain]
  have e5 : q0 + z * (q1 + z * 0) = q0 + z * q1 := by ring
  rw [e5]
  linarith

/-! ### Near nodes -/

def nQ (n d Tz : ℤ) (δ : ℕ) : List ℤ :=
  if 2 * (δ : ℤ) ≤ |Tz| then nodeQ n d Tz δ else innQ n d Tz δ
def nE (n d Tz : ℤ) (δ : ℕ) : ℤ :=
  if 2 * (δ : ℤ) ≤ |Tz| then nodeE n d Tz δ else innE n d Tz δ
def nOK (d Tz : ℤ) (δ : ℕ) : Bool :=
  if 2 * (δ : ℤ) ≤ |Tz| then nodeOK d Tz δ else innOK d Tz δ

theorem n_up {n d Tz : ℤ} {δ : ℕ} (h : nOK d Tz δ = true) {z : ℝ} (hz : |z| ≤ 1) :
    (n : ℝ) / d * Fv (((Tz : ℝ) - δ * z) / Lam) ≤ (evalZ (nQ n d Tz δ) z + nE n d Tz δ) / 2 ^ 64 := by
  unfold nQ nE
  unfold nOK at h
  split_ifs at h ⊢
  · exact node_up h hz
  · exact inn_up h hz

def rho (Tot : ℤ) (t : Tr) : ℤ × ℤ := (t.2.2 * lamZ, Tot * (t.2.1 - t.1))
def wsub (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 * b.2 - b.1 * a.2, a.2 * b.2)
noncomputable def wv (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) / p.2

def nodesL (Tot : ℤ) : ℤ × ℤ → List Tr → List ((ℤ × ℤ) × ℤ)
  | _, [] => []
  | p, [t] => [(wsub p (rho Tot t), t.1), (rho Tot t, t.2.1)]
  | p, t :: u :: r => (wsub p (rho Tot t), t.1) :: nodesL Tot (rho Tot t) (u :: r)

def contig : List Tr → Bool
  | [] => true
  | [_] => true
  | t :: u :: r => decide (t.2.1 = u.1) && contig (u :: r)

noncomputable def nsum (L : List ((ℤ × ℤ) × ℤ)) (y : ℝ) : ℝ :=
  (L.map fun e => wv e.1 * Fv ((e.2 : ℝ) / Lam - y)).sum

theorem wsub_val {p q : ℤ × ℤ} (hp : p.2 ≠ 0) (hq : q.2 ≠ 0) : wv (wsub p q) = wv p - wv q := by
  have h1 : (p.2 : ℝ) ≠ 0 := by exact_mod_cast hp
  have h2 : (q.2 : ℝ) ≠ 0 := by exact_mod_cast hq
  simp only [wv, wsub]
  push_cast
  field_simp

theorem rho_ne {Tot : ℤ} {t : Tr} (hT : 0 < Tot) (hv : Vt t) : (rho Tot t).2 ≠ 0 := by
  have := hv.1
  simp only [rho]
  exact mul_ne_zero hT.ne' (by omega)

theorem cell_closed {Tot : ℤ} {t : Tr} (hT : 0 < Tot) (hv : Vt t) (y : ℝ) :
    (mkCell 1 Tot t).pot y = wv (rho Tot t) *
      (Fv ((t.2.1 : ℝ) / Lam - y) - Fv ((t.1 : ℝ) / Lam - y)) := by
  obtain ⟨h1, h2, h3⟩ := mkCell_eq (m := 1) (T := Tot) (t := t) hv hT.le (by norm_num)
  rw [pot_closed, h1, h2, h3]
  have hTr : (Tot : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hd : (t.2.1 : ℝ) - t.1 ≠ 0 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  have e : (1 : ℝ) * t.2.2 / Tot / ((t.2.1 : ℝ) / 10 ^ 12 - (t.1 : ℝ) / 10 ^ 12) = wv (rho Tot t) := by
    simp only [wv, rho]
    have hl : ((lamZ : ℤ) : ℝ) = 10 ^ 12 := by norm_num [lamZ]
    push_cast
    rw [hl]
    have : (t.2.1 : ℝ) / 10 ^ 12 - (t.1 : ℝ) / 10 ^ 12 = ((t.2.1 : ℝ) - t.1) / 10 ^ 12 := by ring
    rw [this]
    field_simp
  rw [e]

theorem nodes_sum {Tot : ℤ} (hT : 0 < Tot) (y : ℝ) : ∀ (l : List Tr) (t : Tr) (p : ℤ × ℤ), p.2 ≠ 0 →
    (∀ u ∈ t :: l, Vt u) → contig (t :: l) = true →
    wv p * Fv ((t.1 : ℝ) / Lam - y) + potL ((t :: l).map (mkCell 1 Tot)) y =
      nsum (nodesL Tot p (t :: l)) y
  | [], t, p, hp, hv, _ => by
    have hvt := hv t (by simp)
    simp only [nodesL, nsum, potL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [cell_closed hT hvt, wsub_val hp (rho_ne hT hvt)]
    ring
  | u :: r, t, p, hp, hv, hc => by
    have hvt := hv t (by simp)
    simp only [contig, Bool.and_eq_true, decide_eq_true_eq] at hc
    have ih := nodes_sum hT y r u (rho Tot t) (rho_ne hT hvt)
      (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hc.2
    have e1 : potL ((t :: u :: r).map (mkCell 1 Tot)) y =
        (mkCell 1 Tot t).pot y + potL ((u :: r).map (mkCell 1 Tot)) y := by simp [potL]
    have e2 : nsum (nodesL Tot p (t :: u :: r)) y = wv (wsub p (rho Tot t)) * Fv ((t.1 : ℝ) / Lam - y) +
        nsum (nodesL Tot (rho Tot t) (u :: r)) y := by
      simp [nodesL, nsum]
    rw [e1, e2, ← ih, cell_closed hT hvt, wsub_val hp (rho_ne hT hvt), hc.1]
    ring

def nsQ (sc M : ℤ) (δ : ℕ) : List ((ℤ × ℤ) × ℤ) → List ℤ
  | [] => []
  | e :: l => addL (nQ (sc * e.1.1) e.1.2 (e.2 - M) δ) (nsQ sc M δ l)

def nsE (sc M : ℤ) (δ : ℕ) : List ((ℤ × ℤ) × ℤ) → ℤ
  | [] => 0
  | e :: l => nE (sc * e.1.1) e.1.2 (e.2 - M) δ + nsE sc M δ l

def nsOK (M : ℤ) (δ : ℕ) : List ((ℤ × ℤ) × ℤ) → Bool
  | [] => true
  | e :: l => nOK e.1.2 (e.2 - M) δ && nsOK M δ l

theorem ns_up (sc M : ℤ) (δ : ℕ) {z : ℝ} (hz : |z| ≤ 1) : ∀ L : List ((ℤ × ℤ) × ℤ), nsOK M δ L = true →
    (sc : ℝ) * nsum L (((M : ℝ) + δ * z) / Lam) ≤ (evalZ (nsQ sc M δ L) z + nsE sc M δ L) / 2 ^ 64
  | [], _ => by simp [nsum, nsQ, nsE, evalZ]
  | e :: l, h => by
    simp only [nsOK, Bool.and_eq_true] at h
    have ih := ns_up sc M δ hz l h.2
    have h1 := n_up (n := sc * e.1.1) h.1 hz
    have e1 : (e.2 : ℝ) / Lam - ((M : ℝ) + δ * z) / Lam = (((e.2 - M : ℤ) : ℝ) - δ * z) / Lam := by
      push_cast; ring
    have e2 : nsum (e :: l) (((M : ℝ) + δ * z) / Lam) =
        wv e.1 * Fv ((e.2 : ℝ) / Lam - ((M : ℝ) + δ * z) / Lam) + nsum l (((M : ℝ) + δ * z) / Lam) := by
      simp [nsum]
    rw [e2, e1, mul_add]
    simp only [nsQ, nsE]
    rw [evalZ_addL]
    have e3 : (sc : ℝ) * (wv e.1 * Fv ((((e.2 - M : ℤ) : ℝ) - δ * z) / Lam)) =
        ((sc * e.1.1 : ℤ) : ℝ) / e.1.2 * Fv ((((e.2 - M : ℤ) : ℝ) - δ * z) / Lam) := by
      simp only [wv]; push_cast; ring
    rw [e3]
    push_cast at h1 ih ⊢
    linarith

/-! ### Tiling -/

def tileOK : ℕ → List Clu → ℕ → Bool
  | i, [], k => decide (i = k)
  | i, c :: cs, k => decide (c.i = i) && decide (c.i ≤ c.j) && tileOK c.j cs k

theorem tile_le : ∀ (cs : List Clu) (i k : ℕ), tileOK i cs k = true → i ≤ k
  | [], i, k, h => by simp [tileOK] at h; omega
  | c :: cs, i, k, h => by
    simp only [tileOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have := tile_le cs c.j k h.2
    omega

def sumQ (sc Tot Y : ℤ) (dl : ℕ) : List Clu → List ℤ
  | [] => []
  | c :: cs => addL (cluQ sc Tot (Y - c.g) dl c) (sumQ sc Tot Y dl cs)

def sumE (sc Tot Y : ℤ) (dl : ℕ) : List Clu → ℤ
  | [] => 0
  | c :: cs => cluE sc Tot (Y - c.g) dl c + sumE sc Tot Y dl cs

def allOK (Y : ℤ) (dl : ℕ) : List Clu → Bool
  | [] => true
  | c :: cs => pairOK c (Y - c.g) dl && allOK Y dl cs

theorem potL_append (a b : List YCell) (y : ℝ) : potL (a ++ b) y = potL a y + potL b y := by
  simp [potL]

theorem tile_up (src : List Tr) (sc Tot Y : ℤ) (dl : ℕ) (hT : 0 < Tot) {z : ℝ} (hz : |z| ≤ 1) :
    ∀ (cs : List Clu) (i k : ℕ), tileOK i cs k = true → (∀ c ∈ cs, c.chk src = true) →
    allOK Y dl cs = true →
    (sc : ℝ) * potL ((seg src i k).map (mkCell 1 Tot)) (((Y : ℝ) + dl * z) / Lam) ≤
      (evalZ (sumQ sc Tot Y dl cs) z + sumE sc Tot Y dl cs) / 2 ^ 64
  | [], i, k, h, _, _ => by
    simp only [tileOK, decide_eq_true_eq] at h
    subst h
    simp [seg, potL, sumQ, sumE, evalZ]
  | c :: cs, i, k, h, hc, ha => by
    simp only [tileOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [allOK, Bool.and_eq_true] at ha
    have ih := tile_up src sc Tot Y dl hT hz cs c.j k h3
      (fun d hd => hc d (List.mem_cons_of_mem _ hd)) ha.2
    have hk := tile_le cs c.j k h3
    have hc1 := clu_abs (sc := sc) (Tz := Y - c.g) (dl := dl) (hc c (by simp)) hT ha.1 hz
    have e0 : (((c.g + (Y - c.g) : ℤ) : ℝ) / Lam + dl * z / Lam) = ((Y : ℝ) + dl * z) / Lam := by
      push_cast; ring
    rw [e0] at hc1
    have hs : seg src i k = seg src c.i c.j ++ seg src c.j k := by
      rw [h1] at h2 ⊢
      exact (seg_append src h2 hk).symm
    rw [hs, List.map_append, potL_append, mul_add]
    simp only [sumQ, sumE]
    rw [evalZ_addL]
    have := (abs_le.1 hc1).2
    push_cast at ih this ⊢
    rw [h1] at this ⊢
    linarith

/-! ### Units -/

structure UnitD where
  M : ℤ
  δ : ℕ
  c0 : List Clu
  c1 : List Clu
  rw : List Clu
  n0 : ℕ
  n1 : ℕ
  lm : Bool
  rm : Bool

/-- GD6: the table lengths are those of the source tables (628 and 704 for `capSource`). -/
@[irreducible] def lenC : ℕ := col0.length
@[irreducible] def lenR : ℕ := row0.length

theorem col0_len : col0.length = lenC := by unfold lenC; rfl

theorem row0_len : row0.length = lenR := by unfold lenR; rfl

def UnitD.near (u : UnitD) : List ((ℤ × ℤ) × ℤ) := nodesL Tc (0, 1) (seg col0 u.n0 u.n1)

def UnitD.lQ (u : UnitD) : List ℤ :=
  if u.lm then monoQ 9 58 (u.M + u.δ) else logQ 9 58 u.M (-(u.δ : ℤ))
def UnitD.lE (u : UnitD) : ℤ :=
  if u.lm then monoE 9 58 else logE 9 58 u.M (-(u.δ : ℤ))
def UnitD.lOK (u : UnitD) : Bool :=
  if u.lm then monoOK 9 58 (u.M + u.δ) else logOK 9 58 u.M (-(u.δ : ℤ))

def UnitD.rQ (u : UnitD) : List ℤ :=
  if u.rm then monoQ 3 58 (lamZ - u.M + u.δ) else logQ 3 58 (lamZ - u.M) u.δ
def UnitD.rE (u : UnitD) : ℤ :=
  if u.rm then monoE 3 58 else logE 3 58 (lamZ - u.M) u.δ
def UnitD.rOK (u : UnitD) : Bool :=
  if u.rm then monoOK 3 58 (lamZ - u.M + u.δ) else logOK 3 58 (lamZ - u.M) u.δ

def UnitD.Q (u : UnitD) : List ℤ :=
  addL (sumQ 2 Tc u.M u.δ u.c0) (addL (sumQ 2 Tc u.M u.δ u.c1) (addL (nsQ 2 u.M u.δ u.near)
    (addL (sumQ (-1) Trw (2 * u.M) (2 * u.δ) u.rw) (addL u.lQ u.rQ))))

def UnitD.E (u : UnitD) : ℤ :=
  sumE 2 Tc u.M u.δ u.c0 + (sumE 2 Tc u.M u.δ u.c1 + (nsE 2 u.M u.δ u.near +
    (sumE (-1) Trw (2 * u.M) (2 * u.δ) u.rw + (u.lE + u.rE))))

def supB : List ℤ → ℤ
  | [] => 0
  | a :: l => a + bE (0 :: l)

theorem evalZ_le_supB (l : List ℤ) (z : ℝ) (hz : |z| ≤ 1) : evalZ l z ≤ (supB l : ℝ) := by
  cases l with
  | nil => simp [evalZ, supB]
  | cons a l =>
    have h := evalZ_le_bE (0 :: l) z hz
    simp only [evalZ, supB] at h ⊢
    push_cast at h ⊢
    linarith

def LqI : ℤ := (6905432 * 2 ^ 64) / 10 ^ 7 + 1

def UnitD.fin (u : UnitD) : Bool :=
  decide ((supB u.Q + u.E + LqI) * 10 ^ 6 ≤ -2946610 * 2 ^ 64)

def UnitD.ok (u : UnitD) : Bool :=
  tileOK 0 u.c0 u.n0 && tileOK u.n1 u.c1 lenC && tileOK 0 u.rw lenR &&
    decide (u.n0 ≤ u.n1) && decide (u.n1 ≤ lenC) && decide (0 < u.δ) &&
    allOK u.M u.δ u.c0 && allOK u.M u.δ u.c1 && allOK (2 * u.M) (2 * u.δ) u.rw &&
    contig (seg col0 u.n0 u.n1) && nsOK u.M u.δ u.near && u.lOK && u.rOK

/-- All checks of one unit. The cluster tables are checked separately, once per cluster. -/
structure UnitD.V (u : UnitD) : Prop where
  ok : u.ok = true
  fin : u.fin = true
  h0 : ∀ c ∈ u.c0, c.chk col0 = true
  h1 : ∀ c ∈ u.c1, c.chk col0 = true
  hr : ∀ c ∈ u.rw, c.chk row0 = true

theorem seg_full {src : List Tr} {n : ℕ} (h : src.length = n) : seg src 0 n = src := by
  simp [seg, ← h]

theorem seg_mem {src : List Tr} {i j : ℕ} {t : Tr} (h : t ∈ seg src i j) : t ∈ src :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem near_pot (u : UnitD) (hc : contig (seg col0 u.n0 u.n1) = true) (y : ℝ) :
    potL ((seg col0 u.n0 u.n1).map (mkCell 1 Tc)) y = nsum u.near y := by
  unfold UnitD.near
  cases hl : seg col0 u.n0 u.n1 with
  | nil => simp [potL, nodesL, nsum]
  | cons t l =>
    rw [hl] at hc
    have h := nodes_sum Tc_pos y l t (0, 1) (by norm_num)
      (fun w hw => col0_ok w (seg_mem (by rw [hl]; exact hw))) hc
    have e : wv ((0 : ℤ), (1 : ℤ)) = 0 := by simp [wv]
    rw [e, zero_mul, zero_add] at h
    exact h

theorem evalZ_mono (cn cd B : ℤ) (z : ℝ) : evalZ (monoQ cn cd B) z = evalZ (monoQ cn cd B) 0 := by
  simp [monoQ, evalZ]

theorem lQ_up (u : UnitD) (h : u.lOK = true) {z : ℝ} (hz : |z| ≤ 1) (h0 : 0 < (u.M : ℝ) + u.δ * z) :
    9 / 58 * Real.log (((u.M : ℝ) + u.δ * z) / Lam) ≤ (evalZ u.lQ z + u.lE) / 2 ^ 64 := by
  unfold UnitD.lOK at h
  unfold UnitD.lQ UnitD.lE
  have hLam : (0:ℝ) < Lam := by norm_num
  split_ifs at h ⊢
  · have hu : 0 < ((u.M : ℝ) + u.δ * z) / Lam := div_pos h0 hLam
    have hB : ((u.M : ℝ) + u.δ * z) / Lam ≤ ((u.M + u.δ : ℤ) : ℝ) / Lam := by
      apply div_le_div_of_nonneg_right _ hLam.le
      push_cast
      have h1 := (abs_le.1 hz).2
      have hδ : (0:ℝ) ≤ u.δ := by positivity
      nlinarith
    have := mono_up h hu hB
    rw [evalZ_mono _ _ _ z]
    push_cast at this ⊢
    exact this
  · have := log_up h hz
    have e : (((u.M : ℤ) : ℝ) - ((-(u.δ : ℤ) : ℤ) : ℝ) * z) = (u.M : ℝ) + u.δ * z := by
      push_cast; ring
    rw [e] at this
    push_cast at this ⊢
    exact this

theorem rQ_up (u : UnitD) (h : u.rOK = true) {z : ℝ} (hz : |z| ≤ 1)
    (h0 : (u.M : ℝ) + u.δ * z < Lam) :
    3 / 58 * Real.log (1 - ((u.M : ℝ) + u.δ * z) / Lam) ≤ (evalZ u.rQ z + u.rE) / 2 ^ 64 := by
  unfold UnitD.rOK at h
  unfold UnitD.rQ UnitD.rE
  have hLam : (0:ℝ) < Lam := by norm_num
  have hl : ((lamZ : ℤ) : ℝ) = Lam := by norm_num [lamZ, Lam]
  have e1 : 1 - ((u.M : ℝ) + u.δ * z) / Lam = (Lam - u.M - u.δ * z) / Lam := by
    field_simp
    ring
  rw [e1]
  split_ifs at h ⊢
  · have hu : 0 < (Lam - (u.M : ℝ) - u.δ * z) / Lam := div_pos (by linarith) hLam
    have hB : (Lam - (u.M : ℝ) - u.δ * z) / Lam ≤ ((lamZ - u.M + u.δ : ℤ) : ℝ) / Lam := by
      apply div_le_div_of_nonneg_right _ hLam.le
      push_cast
      rw [hl]
      have h1 := (abs_le.1 hz).1
      have hδ : (0:ℝ) ≤ u.δ := by positivity
      nlinarith
    have := mono_up h hu hB
    rw [evalZ_mono _ _ _ z]
    push_cast at this ⊢
    exact this
  · have := log_up h hz
    have e : (((lamZ - u.M : ℤ) : ℝ) - ((u.δ : ℤ) : ℝ) * z) = Lam - u.M - u.δ * z := by
      push_cast; rw [hl]
    rw [e] at this
    push_cast at this ⊢
    exact this

set_option maxHeartbeats 800000 in
theorem unit_field {u : UnitD} (hu : u.V) {z : ℝ} (hz : |z| ≤ 1) (h0 : 0 < (u.M : ℝ) + u.δ * z)
    (h1 : (u.M : ℝ) + u.δ * z < Lam) :
    capSource.colField 0 (((u.M : ℝ) + u.δ * z) / Lam) ≤ ((cq : ℚ) : ℝ) := by
  obtain ⟨hok, hfin, hc0, hc1, hcr⟩ := hu
  simp only [UnitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t0, t1⟩, tr⟩, hn⟩, hn1⟩, hδ⟩, a0⟩, a1⟩, ar⟩, hct⟩, hns⟩, hl⟩, hr⟩ := hok
  have T0 := tile_up col0 2 Tc u.M u.δ Tc_pos hz u.c0 0 u.n0 t0 hc0 a0
  have T1 := tile_up col0 2 Tc u.M u.δ Tc_pos hz u.c1 u.n1 lenC t1 hc1 a1
  have T2 := ns_up 2 u.M u.δ hz u.near hns
  have T3 := tile_up row0 (-1) Trw (2 * u.M) (2 * u.δ) Trw_pos hz u.rw 0 lenR tr hcr ar
  have T4 := lQ_up u hl hz h0
  have T5 := rQ_up u hr hz h1
  set y : ℝ := ((u.M : ℝ) + u.δ * z) / Lam with hy
  have e3 : ((((2 * u.M : ℤ) : ℝ)) + ((2 * u.δ : ℕ) : ℝ) * z) / Lam = 2 * y := by
    rw [hy]; push_cast; ring
  rw [e3, seg_full row0_len] at T3
  rw [← near_pot u hct] at T2
  have hsp : col0 = seg col0 0 u.n0 ++ (seg col0 u.n0 u.n1 ++ seg col0 u.n1 lenC) := by
    rw [seg_append col0 hn hn1, seg_append col0 (Nat.zero_le _) (hn.trans hn1), seg_full col0_len]
  have hcol : potL (capSource.refCol 0) y = potL ((seg col0 0 u.n0).map (mkCell 1 Tc)) y +
      (potL ((seg col0 u.n0 u.n1).map (mkCell 1 Tc)) y +
        potL ((seg col0 u.n1 lenC).map (mkCell 1 Tc)) y) := by
    rw [refCol0]
    conv_lhs => rw [hsp]
    rw [List.map_append, List.map_append, potL_append, potL_append]
  have hrow : potL (capSource.refRow 0) (2 * y) = potL (row0.map (mkCell 1 Trw)) (2 * y) := by
    rw [refRow0]
  have hLc : ((Lq : ℚ) : ℝ) ≤ physL (capSource.refRow 0) (fun u => Real.log |u|) := L_cert
  have hLq : ((Lq : ℚ) : ℝ) = -6905432 / 10 ^ 7 := by norm_num [Lq]
  rw [hLq] at hLc
  have hLI : (6905432 : ℝ) * 2 ^ 64 / 10 ^ 7 ≤ LqI := by
    have := floor_up (6905432 * 2 ^ 64) (10 ^ 7) (by norm_num)
    unfold LqI
    norm_num at this ⊢
  simp only [UnitD.fin, decide_eq_true_eq] at hfin
  have hfr : (((supB u.Q + u.E + LqI) * 10 ^ 6 : ℤ) : ℝ) ≤ ((-2946610 * 2 ^ 64 : ℤ) : ℝ) := by
    exact_mod_cast hfin
  push_cast at hfr
  have hsup := evalZ_le_supB u.Q z hz
  have hQ : evalZ u.Q z = evalZ (sumQ 2 Tc u.M u.δ u.c0) z + (evalZ (sumQ 2 Tc u.M u.δ u.c1) z +
      (evalZ (nsQ 2 u.M u.δ u.near) z + (evalZ (sumQ (-1) Trw (2 * u.M) (2 * u.δ) u.rw) z +
        (evalZ u.lQ z + evalZ u.rQ z)))) := by
    simp only [UnitD.Q, evalZ_addL]
  have hE : (u.E : ℝ) = (sumE 2 Tc u.M u.δ u.c0 : ℝ) + ((sumE 2 Tc u.M u.δ u.c1 : ℝ) +
      ((nsE 2 u.M u.δ u.near : ℝ) + ((sumE (-1) Trw (2 * u.M) (2 * u.δ) u.rw : ℝ) +
        ((u.lE : ℝ) + u.rE)))) := by
    simp only [UnitD.E]; push_cast; ring
  rw [hQ] at hsup
  rw [hE] at hfr
  have hcq : ((cq : ℚ) : ℝ) = -2946610 / 10 ^ 6 := by norm_num [cq]
  rw [hcq]
  unfold CapSource.colField
  rw [hcol, hrow]
  push_cast at T0 T1 T2 T3
  have ey : (((u.M : ℝ) + u.δ * z) / Lam) = y := rfl
  have e2 : (((2 : ℝ) * u.M + 2 * u.δ * z) / Lam) = 2 * y := by rw [hy]; ring
  linarith

/-- The cap on the whole `s`-range of one unit inside `(0,1)`. -/
theorem unit_range {u : UnitD} (hu : u.V) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (h1 : ((u.M - u.δ : ℤ) : ℝ) / 10 ^ 12 ≤ s) (h2 : s ≤ ((u.M + u.δ : ℤ) : ℝ) / 10 ^ 12) :
    capSource.colField 0 s ≤ ((cq : ℚ) : ℝ) := by
  have hok := hu.ok
  simp only [UnitD.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hδ : 0 < u.δ := hok.1.1.1.1.1.1.1.2
  have hδr : (0:ℝ) < u.δ := by exact_mod_cast hδ
  have hL : (Lam : ℝ) = 10 ^ 12 := by norm_num [Lam]
  push_cast at h1 h2
  rw [div_le_iff₀ (by norm_num)] at h1
  rw [le_div_iff₀ (by norm_num)] at h2
  set z : ℝ := (s * 10 ^ 12 - u.M) / u.δ with hz
  have hzz : (u.M : ℝ) + u.δ * z = s * 10 ^ 12 := by
    rw [hz]; field_simp; ring
  have hz1 : |z| ≤ 1 := by
    rw [abs_le, hz]
    constructor
    · rw [le_div_iff₀ hδr]; linarith
    · rw [div_le_iff₀ hδr]; linarith
  have h := unit_field hu hz1 (by rw [hzz]; positivity) (by rw [hzz, hL]; nlinarith)
  rw [hzz, hL] at h
  have e : s * 10 ^ 12 / 10 ^ 12 = s := by field_simp
  rwa [e] at h

/-- `UnitCap` of an interior unit. -/
theorem unit_cap_of {u : UnitD} (hu : u.V) (h0 : 0 < u.M - u.δ) (h1 : u.M + u.δ < lamZ) :
    UnitCap (u.M - u.δ, u.M + u.δ) := by
  intro s hs1 hs2
  have r0 : (0:ℝ) < ((u.M - u.δ : ℤ) : ℝ) := by exact_mod_cast h0
  have r1 : ((u.M + u.δ : ℤ) : ℝ) < 10 ^ 12 := by
    have : ((u.M + u.δ : ℤ) : ℝ) < ((lamZ : ℤ) : ℝ) := by exact_mod_cast h1
    have e : ((lamZ : ℤ) : ℝ) = 10 ^ 12 := by norm_num [lamZ]
    rwa [e] at this
  refine unit_range hu ?_ ?_ hs1 hs2
  · exact lt_of_lt_of_le (by positivity) hs1
  · refine lt_of_le_of_lt hs2 ?_
    rw [div_lt_one (by norm_num)]
    exact r1

def rng (u : UnitD) : ℤ × ℤ := (u.M - u.δ, u.M + u.δ)

/-- **Generic consumer.** A left end unit, interior units chained from `a` to `b`, and a right end
unit, each with its finite checks, give the `hC` input of T4 for the anchor-0 free column. -/
theorem freeColCap_of_units (uL uR : UnitD) (us : List UnitD) (a b : ℤ)
    (hL : uL.V) (hR : uR.V) (hV : ∀ u ∈ us, u.V)
    (hin : ∀ u ∈ us, 0 < u.M - u.δ ∧ u.M + u.δ < lamZ)
    (hch : chain a (us.map rng) b = true)
    (hLa : uL.M - uL.δ ≤ 0) (hLb : a ≤ uL.M + uL.δ)
    (hRa : uR.M - uR.δ ≤ b) (hRb : lamZ ≤ uR.M + uR.δ) (ha : a < lamZ) (hb : 0 < b) :
    capSource.FreeColCap 0 (-2946610 / 1000000) := by
  refine freeColCap0_of_cover a b (us.map rng) hch ?_ ?_ ?_
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    exact unit_cap_of (hV u hu) (hin u hu).1 (hin u hu).2
  · intro s hs0 hs
    have hs1 : s < 1 := by
      have r : (a : ℝ) < ((lamZ : ℤ) : ℝ) := by exact_mod_cast ha
      have e : ((lamZ : ℤ) : ℝ) = 10 ^ 12 := by norm_num [lamZ]
      rw [e] at r
      refine lt_of_le_of_lt hs ?_
      rw [div_lt_one (by norm_num)]
      exact r
    refine unit_range hL hs0 hs1 ?_ ?_
    · have : ((uL.M - uL.δ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hLa
      exact (div_nonpos_of_nonpos_of_nonneg this (by norm_num)).trans hs0.le
    · refine hs.trans ?_
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast hLb
  · intro s hs hs1
    refine unit_range hR ?_ hs1 ?_ ?_
    · have r : (0:ℝ) < b := by exact_mod_cast hb
      exact lt_of_lt_of_le (by positivity) hs
    · refine le_trans ?_ hs
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast hRa
    · have : ((lamZ : ℤ) : ℝ) ≤ ((uR.M + uR.δ : ℤ) : ℝ) := by exact_mod_cast hRb
      have e : ((lamZ : ℤ) : ℝ) = 10 ^ 12 := by norm_num [lamZ]
      rw [e] at this
      rw [le_div_iff₀ (by norm_num)]
      nlinarith

/-! ### One real unit: the unit containing the measured supremum -/

set_option maxRecDepth 100000

def UBC0 : Clu := ⟨0, 157, 70374981957, 64352290770, 5, raw_ints% [155262417196, -2560114295745449339487, 664392235294865769976022888352667, -11951832284641949520499942390395226410491569, 2735588963154168248274091917301275919621424286906252677, -48889216007017504297393264973137842033390311211330981915908857655]⟩

theorem UBC0_chk : UBC0.chk col0 = true := by
  -- kcost: 157 cells x 6 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC1 : Clu := ⟨157, 235, 280090909091, 145363636364, 9, raw_ints% [198009081882, -3260023985148969292554, 4298711121774764133427343279627874, -84916177159390400472470397450515233432538694, 91923954257329968150900235464304414734765521756350053942, -1951782015101567015621479819410182953211216034854340919706236950894, 1955592779722974049603540818726409493447471637889231169776963172268746048753454, -43186609354501961902293168788004414525421360479753515463151653872694962902256030573430294, 41503777766320425699755461288092822978127202323395218220407573498040049510741214243838254792552168982, -939611037041145324562798027395435365363954872744158949515078843188654031976595266443036136768036697240354663934]⟩

theorem UBC1_chk : UBC1.chk col0 = true := by
  -- kcost: 78 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC2 : Clu := ⟨235, 314, 572681818182, 147227272727, 14, raw_ints% [184535937513, 1346831796903794757452, 4064997116434262548687722458680524, 35630789223709549188680686148483849479794512, 88729603710527061959214279887769937738631980951962254808, 835318908694842944609559910461364632459157753313710008452776552532, 1930822119153406967222052622956319330049955092470697664839501141996375227382784, 18889406779058663132474591486006912684936164706760728157056512603404658413401920777537832, 41956981268228218238663807958719469626238890321186709126163989410574543322162450074790295095325401368, 420476938370870046833437208919908470617877387843009506383295373875326656350605720774977539195187050964625306012, 911033738599910614345965275676629950041945204346473444368566205844954214093169959564883715865990569910282293714637098427344, 9282174205774827220714558899439294744112064837698588283151885016781686224826043921326916940770516771517045264249843470227840899167152, 19772632138947020438798412477314793232681216588425871628370883735531140866648911992380740587111527923353763459691163816540824259759494354883025128, 203896142396026844570361993832315832771823996704515501020475707786434679094745131825840413309144688336374656562876032594831600519342470758019745750713029092, 429006974188952710736519339931317273256075625991324137961677467087312665516329502824636014236679136411727092706566609373611880944478186508047099515175139650111808628704]⟩

theorem UBC2_chk : UBC2.chk col0 = true := by
  -- kcost: 79 cells x 15 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC3 : Clu := ⟨314, 353, 792590909091, 72681818182, 14, raw_ints% [119209604802, 1024178478428138623187, 639927987534280379294409594602478, 6569405903114521051055489098341173030423669, 3404083899243143846043543722214107060331017862070795932, 37420187181544580783738028835845015566898745865637505589822434847, 18052479955038165723757096610910123545911734889371140018134547234925508501638, 205797652364276786070259238508202784846344267010398278357015743269305599178645455822969, 95600728370377572602802344854074332374666173825243430561667581519506093062385284121870177580158432, 1114698606898115216222201852811370784363133195576347113724053481756831516054503804206020969290226835992593907, 505886344296893433384707653195080366626170006733545135577171037263094546192690692958483866649586983922996177168181529498, 5989547277797248582064451433393642305500999744116745698384013430997135097564772929000384205018659705098842086897946183725763369869, 2675739280859535071192797766018702665447080769251054248683293261156860955915519752653899410258018659799943633268989766080757182438807851583732, 32031041585041356378207770382330474457224663228576416325926836387345326859197184344891829098760609001200770385872015668623989478069821323193946235536967, 14148289291053588232125509264312783578639038219967517009682260337504982664310908830991620128210785928862723445639312051238696812013950505022297693326623539984056558]⟩

theorem UBC3_chk : UBC3.chk col0 = true := by
  -- kcost: 39 cells x 15 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC4 : Clu := ⟨353, 392, 888673677069, 23400949797, 9, raw_ints% [52858460655, 100405927995827960853, 29124827425980408003663496131858, 66144805504108530646917479097693360749395, 15992846712229695028956977763018805645580909032046512, 38835212155535122675205628803974868162292165850274464044535925, 8771809990235979348770266282876517734742786440697921099643979543810746170, 22052136540017374595801803290433720327380971652545956421476370051976877538708150487, 4808658680911277679352517377808759772726057932425601558679683853565091293291330393729824743604, 12344512825907381258358528211012244490860225850402003548771837194799679799481381026630630624162293978457]⟩

theorem UBC4_chk : UBC4.chk col0 = true := by
  -- kcost: 39 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC5 : Clu := ⟨392, 471, 936044776119, 23970149254, 15, raw_ints% [76705295328, 293913047629155442342, 45004880499126857621548015315158, 205281245804068136052832314368456753361376, 26094915017735169717740173020861964227773495104683858, 127283783260805150098328142080967132847783203775063293852051292, 15070189940293801268132741917263218313944092228955851070263067852497401438, 76187987399457434386176220409171751980642878770495159190038139986950164209575153776, 8687288129281585331733350050537527490096159856047995590721703427821692585585850114590111799338, 44910285425226310751197897259000598367859222513271695517841852206788503180725703396629398199465974652292, 5002834413512677827699044491296737488367798614451529815196831105810212927741146976170573261543567600802025188381718, 26260407786630636723753394827659294695666149661006564891384731308592894032630469225523682353465187835208019138549014751597176, 2879292369262499260024173153820517633567611041667392236076890309955753663431229518304557968365115758400288421138900844754723635444579618, 15282054831539276005353726797668978391441170129379761441234969096710237045927026679639388264795864293114507715242897703187074945525059807213042892, 1656473814828156075712676945405559737996301176957251091175853118865204067909136565686675333808229347507180100004702452223465650310363838584205902297162065998, 8866044959343183589399299864852979034832123612757145260580204890771235933152313678342707313478355744558152342558902274881670032906103194772769546240925978740486600576]⟩

theorem UBC5_chk : UBC5.chk col0 = true := by
  -- kcost: 79 cells x 16 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC6 : Clu := ⟨471, 510, 970850746268, 10835820896, 14, raw_ints% [56948383168, 102395126502681917085, 6830498008806313611787591228672, 14602801252029262761512482505292635731955, 809434475736453839943024621798264572305796767843460, 1849054493935160339158159662458400627986328500325908327593267, 95530742603938679369646762914178258633771255921687944746091847153945420, 226036929534156143017467638604058259925652384761869963967485970507987063256888443, 11253594631133111240084663800578236349185293196455761838572977283444394828713766578678543652, 27212479781435767893423306605722488233094552644577881276561934419063777331234336056287861369861138019, 1324332102321315294599017060995699817534605740326016276329899934027565958409810574303411133997543112638144556348, 3249829907027940575082138270340578416022728705412749338317049711160050284720043203015169616488413116630940747952651361611, 155752420433414338871305286177521951876249758875376770774441776201971652991334723957337206426239328738049291961265938665469760276564, 386262616378271031087697378161836330496277193168367774945835597457790038008411877597408248322214396723043592957251772210582555581715387341491, 18310418148890733770196949184730217193980965068300019758950766107232585993646775591103866021691685461598494573696756417289198016995992886298522694050156]⟩

theorem UBC6_chk : UBC6.chk col0 = true := by
  -- kcost: 39 cells x 15 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC7 : Clu := ⟨510, 549, 985843283582, 4156716418, 11, raw_ints% [34634484471, 18948874767799525409, 606420450941880326758797117543, 395461087427008001362202737746268044479, 10538519150991244345922672859495992625153408476895, 7344423643175972643878539458430237655721804843636160329431, 182679046911440279440698217703644176847946403397780514696801233550799, 131821980199589469308062452774701272815516653209491178549693553093355578601767, 3162962864914683516105757516377235929791706856458195900108637424009078744367377188726719, 2331495545857389233186280382705997325943413104561482149268246899065619247482728174753372280677783, 54729978115190210324785566695686394222798095647330079503734588255801771494996594619798611503748774277563695, 40921020869782833711044695373678486434917876339956782079670392981301375004676172498795510613880435491158968739530375]⟩

theorem UBC7_chk : UBC7.chk col0 = true := by
  -- kcost: 39 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC8 : Clu := ⟨549, 568, 991875000000, 1875000000, 9, raw_ints% [22401073263, 4326629540142240840, 79373883109109173923272489430, 18286869550535211636624476804663721960, 279956680102960011080495903158807845702491699670, 68873279686558498491046430100616880122676094954157296840, 985903831215255620006059238891788325313994863004152951065212217430, 250854804960619540655123665567086514807907094860318058029868051613281432360, 3469553774036294891585783357835623152417337330912361409886842166078747667982065328470, 900697378614906231528990086527649494135900872726951568110881487378836884974265280748766834440]⟩

theorem UBC8_chk : UBC8.chk col0 = true := by
  -- kcost: 19 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC9 : Clu := ⟨568, 588, 995434691472, 1684691472, 13, raw_ints% [29999405002, 8536677468958237449, 86974119477640782434825280925, 29376184702468922388782948112786330739, 249142654907170874335320994905400113610976366609, 89791614074235608540708903650020396476292433669653202115, 710820028597252696774121151764307160475913993495166469499899341593, 265055116773758084001059874916792730823300726541089655371467221455783694443, 2024312501425782540827771114142651428502476210719095357820980393244321368303663750961, 770752517841920770750448369778503090026490865429401987918470337137925066275285057463280499891, 5759303048895269216849708656307959432705219807538454379939219111012735314120583563585288844886646208841, 2223783493138059379677308022983159493899120683664676172899866301650986435532165536364049847154384428207176025787, 16375988007178180711510023539068009339847453966397188191590241253752390735238808955015708534216729567924689692303081260833, 6386644415133233108590690349408560560023604886078161776790550866359740501554689815279528762889891362681468691890078684300946644227]⟩

theorem UBC9_chk : UBC9.chk col0 = true := by
  -- kcost: 20 cells x 14 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC10 : Clu := ⟨588, 598, 997870800545, 751417602, 13, raw_ints% [22075968253, 2613721516296689242, 12680926949356629072526664673, 1774760028556335585698324236998371956, 7206931343447665673151997422848945370759645015, 1071097323306827996643524241162214187190048774452163118, 4081417027896621789757221768396311063815987781307687518733158637, 624576559696322041941828228717597114859859930266108609555017048946525432, 2307779167842984336354027213727180225333790991878375320831281891552072080971586979, 358943166095985933832343762895713395108516124476187911484372348828613287304883661652606274, 1303903378967321466997933119695782649874725936022789226012174968476250582507823692419293876319402841, 204774210033702655044997241854913090457957976925613830387113336815758922392840966553991990814130482459683468, 736427209520814033176636786261454914549876374238735605356286322797654560572017961176987141226632295914072871103399183, 116345263633356128909047930434472171356224082755294026685999065370934005864407074927476790406512306305928810698458418767339990]⟩

theorem UBC10_chk : UBC10.chk col0 = true := by
  -- kcost: 10 cells x 14 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC11 : Clu := ⟨598, 603, 998938520463, 316302316, 11, raw_ints% [14517918741, 573696765842988326, 1471680577296766295739847547, 67553890078634779280312692095639238, 148086567396888563021750740750864563428830285, 7100633113282827759255805142801839196307232703656152, 14859715368490175617377488756356307212694335730282689326726051, 724191092053412422929564580246819906682628584539233024119063215497074, 1488965603608132628639527928765138819684429097160462551119581425353802677617289, 73060862700882504403567407165581839888594245028009659194551644207374614891498407621868, 149082270046666811650343256060348628021135241894859394679480420370771873789427995103057582924015, 7337452946276994482558408982965107733505526123463122022932008765362619983533047765144772378494254538150]⟩

theorem UBC11_chk : UBC11.chk col0 = true := by
  -- kcost: 5 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC12 : Clu := ⟨603, 608, 999425895783, 171073004, 11, raw_ints% [11544424329, 235639927248245415, 341963911988368108360472154, 8110741868510640995129972698698015, 10061466001218529415304592589506787809379934, 249287289362063792803279435518788952006902008247955, 295277273104996106839239610044788849631865878680544004053234, 7435793590794551939995022562518109138616135602530724683473706850855, 8654083372456266145454212925225428533388082455267310875386561956250233267814, 219418406795533581079867486362503772173261471937617850988737236632538664543820647195, 253454748050450028371819384579140093064200584067461202019589757009038809957195457181993686714, 6445699477967843042095479876017037100947776045611452044293495544060709891660280305142209400677878895]⟩

theorem UBC12_chk : UBC12.chk col0 = true := by
  -- kcost: 5 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC13 : Clu := ⟨608, 613, 999689494106, 92525320, 11, raw_ints% [8957468070, 90158152694020897, 77462317429219002520008029, 906341562354960392986429185943287, 666181381810912698706706754213284309086765, 8141998935137103250968921951767365668261042373187, 5716902016392168015724986191673349620522762045045060164049, 71011330800049805929191722948356355373226119073490445417924656647, 49004066480336982532420415376067010072139428857725655169966704189771811045, 612824453227062917478194503468911077927261597915001788208209151437150873258833227, 419789558395775304471035827653850940560132855730845048635500431305688897668714967294762969, 5265555708193304063000945652820471243653336042939120693530128902844564108954559851319332033916207]⟩

theorem UBC13_chk : UBC13.chk col0 = true := by
  -- kcost: 5 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC14 : Clu := ⟨613, 618, 999832062007, 50042582, 13, raw_ints% [6622234300, 28787656991840136, 16680816127270983868579720, 84242559483513020271200281723464, 41893903300927500487779360342145445631640, 220808638744827235329167771501670153980139909576, 105083760885405309354326811541198748611972250589096635800, 562581237164945960611282612683807393859903240017553446183742344, 263389045022763377554053072085458220499405024138454714586922200584673240, 1419239291404083641718016076660491740544762004858855624101555589491902996467016, 659893212276598529852566908277788180486156209142090956975603591290292904605730546086680, 3565955208817884915052154613227415053516326192159787762862849761738172901834444133617570422024, 1652915712455408301779350706643244627669123466007841136947607823050660216410060600198655727750486730840, 8943858804510703107487554874557326163150983860242666555752605617860585470781841437769833384075032131648134856]⟩

theorem UBC14_chk : UBC14.chk col0 = true := by
  -- kcost: 5 cells x 14 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC15 : Clu := ⟨618, 620, 999894952546, 12847958, 7, raw_ints% [2019789163, 433867850675868, 333748791238938705422611, 71888758105318333098404832564, 55092129841024271641854945493056769315, 11866901091093531325014315742446527934419004, 9094058673891144458359905517736448985512636484237459, 1958878703033334497613963742947380565400532814660029882628]⟩

theorem UBC15_chk : UBC15.chk col0 = true := by
  -- kcost: 2 cells x 8 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC16 : Clu := ⟨620, 623, 999922018218, 14217715, 13, raw_ints% [2332457045, -32066309403261, 470017465251407822660025, -10575873401097641690739948901, 94970643690258024804561338763889450945, -2316900994195485729976022220860300504554541, 19196431530145675357831573049362501332443397220084265, -474992276381293008911237172231934786585969767279846766581, 3880390282713153198716564420416777870828079298779879991056517026385, -96248947975641046244553879133269145347836164741514634523474650667124221, 784393885349532248580824184928321451281908595774011498596814974548435531119326905, -19463544043497268955367841217811626606497108665583026754724436811671208252630907048261, 158560002465588517088906578314791473327802886730876101626282385567997864738772763719500909712225, -3934554082582521282035043619168221271167175952049714412771964750024296377439637111913493867935485901]⟩

theorem UBC16_chk : UBC16.chk col0 = true := by
  -- kcost: 3 cells x 14 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC17 : Clu := ⟨623, 624, 999939923632, 3687700, 6, raw_ints% [575442196, 575442196, 7825511851152302092996, 15651023702304028743796, 106420134217146691477752269132234596, 319260402651400946874001047612565396, 1447220984673189534425874460464503764190201736196]⟩

theorem UBC17_chk : UBC17.chk col0 = true := by
  -- kcost: 1 cells x 7 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC18 : Clu := ⟨624, 625, 999946872486, 3261155, 9, raw_ints% [455467722, 455467722, 4843957829809437569862, 9687915659618419672002, 51516114805989177023027188388715942, 154548344417943311279932519344701682, 547880509688192782104908582789691982445216595222, 2191522038752049902812350618311264783799933362562, 5826779717893720402294841551099621766196986970606848776389702, 29133898589452165596183568463065427126902339748385288379482642]⟩

theorem UBC18_chk : UBC18.chk col0 = true := by
  -- kcost: 1 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC19 : Clu := ⟨627, 628, 999963257647, 2255376, 1, raw_ints% [1480, 1480]⟩

theorem UBC19_chk : UBC19.chk col0 = true := by
  -- kcost: 1 cells x 2 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC20 : Clu := ⟨0, 138, -6523414725785, 4097901063690, 20, raw_ints% [198130661043, 973982022377200091596231, 5203101821368376755468023529487253007, 22761024290151205047763875327627158507147658665199, 105330484911273408845571493658912522757676338363308688449147489, 447278988943221029890528540603350142211774727577628893051653822976276185017, 1971452787435847652081933561831747598218844310063920543156105414462364982669498261330859, 8268706618822775898271452071461279959071944260213764425077761341416484954658716259393536867943285947, 35595798463763808275507368726626614038256458816573005304941004803540516245347600508329793461754794243351635621637, 148341104055094267899267954907383164775159079545234155983346075752435958425546149146094747533042792305655077252100493964172013, 629994071178977740378714219936876734177424889604053360834853568050126265851589048794365605735097446472665646253698223694157821503746705711, 2615456459538106166310855484076813718384086222022756886133648116044193279618804545630791996695148761384948516542525416054908555548464144469618076385135, 11012391004895063915950119114664253124926737575719512601231359541302468063696311974749999762776328517774672367111133684771262579823151992437551281532401274707942825, 45605873571394131402281037048184069312268212675236211697309980449938691145097381311014278089117703605742189275474132512396455275121114163194315153595293712672698876505560726209, 190903131003851953024974715531885712676518119194383398267890821697883452387408762878744007142176548045925365278273073683124051996325935522623497252358879748249377491215708263490468914357363, 789237500177174841212480436283843987944311668414722507212314678116328808486523255145312626351820139891585583210783916473273993103434444391259722895901687535162999528779436678095424737093591350305889763, 3289945545028936631753142908953642353023098690631708290143794418935231716304878653027814860347085630418515561872102487933608897737760410119468347695117347491520200015418625200369327573298531018897671611152195219853, 13584329092005467151190729333440207676559216666052712240839824174218744228684211135004745011900053852407217597609544141077138620366334477279229415823625014748105770031208049408918981359829584855911636526803289942908416971957205, 56452318485758095801202990870887543534580556456625715003097165765156080558907208501794462598140097808590055642371795639885463804910859569408573340521057960396236999738137954344359222678535362444241365897670265464380292834344271976552660215, 232870717426953571790596610627439010291794591795846435061715278964868416224554148296501078213758150892096334498900419025367738744060416483300639473272528817167327081759657877118566281073771410757125135307124438239471103014967238212790496958471722535831, 965479935516281939437962898809576120977463827438626488805565128708903782012908017786808623448447161524538008278475081260886382094629507132902689412184941077569594872654167912961103299854825942984616087117249897594697081708697351885704880194210117089330275582585521]⟩

theorem UBC20_chk : UBC20.chk row0 = true := by
  -- kcost: 138 cells x 21 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC21 : Clu := ⟨138, 277, -2212756831048, 212756831048, 4, raw_ints% [166972666064, 26679360011471104227078, 10879284469448531338815475940796759, 1849732717600715636290218619181461517452729014, 604113753503004261212347467656568707428291558865685424151]⟩

theorem UBC21_chk : UBC21.chk row0 = true := by
  -- kcost: 139 cells x 5 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC22 : Clu := ⟨277, 290, 2000080002619, 46771093, 9, raw_ints% [6642965266, 50298881354253652, 11998819574238804362094573, 185041190712213478262696531750556, 23081553798862943620885335335980490033123, 511455776111221875920904335281397641597929182402, 46068379763851935756021504898528444376182606671720480733, 1276798538058506678542609194694110225546811216191964765283096656, 94264733640671448589353364113134448219876570404595085009808824381482423, 3033583298027356995950837497890713206986746563370086265607891375390334446935022]⟩

theorem UBC22_chk : UBC22.chk row0 = true := by
  -- kcost: 13 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC23 : Clu := ⟨290, 303, 2000213702728, 86929016, 9, raw_ints% [9900314617, -124028432842049169, 75857760551438780490648407, -1125607715249916653646000790663009, 576593235126824894174349003618272493435531, -9096877846653313892682358705641777796890724741349, 4371093721123020720463191196050389500153010256867876747655, -71083467375203477224613949120790156385636293084771439278428482361, 33097005871398198016625320874206549499707928745752632897934565011467006595, -547545504280901945975917173593436110726952705878330001430026767603091260539892269]⟩

theorem UBC23_chk : UBC23.chk row0 = true := by
  -- kcost: 13 cells x 10 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC24 : Clu := ⟨303, 330, 2000588691755, 288060012, 14, raw_ints% [18491285587, -1164330368242337274, 1587233841989494927086437588, -118002498226281769704383605292115872, 133662437354942509682621962134546725093361244, -10592382099711466603402391997657708420049620878824144, 11183344527292623085382183313546282306590509537878843206585760, -916924349712910787869120842563600398932246227406331974326964995390328, 932909600081822421878906728082574701356063345876372296821934151481897972072036, -78123174460391544709338894456785574794129665193709583212298916880746310754694758609904, 77696555739995815700823573640322383013941831319802198042817882904595006970769468605608369153592, -6600582326037225467823174755631920404727705627697176627443688593833332052199886295647389737634818891544, 6464521215779223089126759543543052749425590910210217833553851975752180298943503128317384805188301871968276424668, -554907850450766404251428856237199358961174094028889340523983920841578408496928532278284660478512774394716910714561720304, 537516826942331107243616792127480409045965933348929054573212712632673829882948778863994506675455466298931064240128560563083762384]⟩

theorem UBC24_chk : UBC24.chk row0 = true := by
  -- kcost: 27 cells x 15 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC25 : Clu := ⟨330, 356, 2001345810780, 469059013, 11, raw_ints% [17141199661, -1302013193683596065, 3842303374110987051203077277, -346972862372251744885446642343416137, 852197137651459613532597225179645239360836217, -82184826825841439227037956035495640831895545906127381, 188340151048254883867991837022322419707530241236613624681925117, -18802316967648661185085045604507328249355559460465236479480251073736513, 41556328375342904776244347746556220079167097143016002056564897600212959848826657, -4237414255910416121463228470441999000136802204865638584271231694349000138819888555961037, 9161087917838318540065470198180870985327598977730419161346583060288101018652931541686891134943397, -947459830034858484027856729615169940612456231337143960065025069924357221055085080558979313408735066244089]⟩

theorem UBC25_chk : UBC25.chk row0 = true := by
  -- kcost: 26 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC26 : Clu := ⟨356, 383, 2002462553833, 647684041, 8, raw_ints% [15477056860, -1242921392481764636, 6564333149436924437445422298, -628857015810475388222078146276764112, 2766859895923939369319012325162166084433422010, -283348731540614928927704025604942565117649430065176232, 1163802779382902746356128335996013968700374910460144691434774130, -123429505241698730226134386294674940226796229123069630594621916681011088, 489057223840996544072651446674984179072202998672891247886946571762070168251050826]⟩

theorem UBC26_chk : UBC26.chk row0 = true := by
  -- kcost: 27 cells x 9 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC27 : Clu := ⟨383, 436, 2004969932673, 1859694800, 12, raw_ints% [27546636485, -9417782097523446039, 97560651789025567452581211964, -39578278737976532513546122029672285363, 340906796351136606365069086102439196155052184416, -147674248972585643986374937466981888822302608288889378551, 1185850754497620045050697594245803138917717996275101945890738834188, -531942085264389037307714858001120742511349558488924941409937173125092313611, 4116433010845057871687159133864711822802902797199812471836614159740205358058860815832, -1887045993264804615488087938242123070047679920443873205145264492499503884248869714743302139423, 14273195014111835212070870490876232490766804406626645237404384585807341335101267850632123135500541877732, -6640566236890344946967052963839280002441912672108634773809811230655650552214789741154638647198479520998707082099, 49456635843073605547623745067440545460005650065280503469544275134173078967166576224549046910678982587353528406780878842928]⟩

theorem UBC27_chk : UBC27.chk row0 = true := by
  -- kcost: 53 cells x 13 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC28 : Clu := ⟨436, 463, 2008115372741, 1285745268, 6, raw_ints% [13093891361, -1282387616418010786, 21735207889052181578990279826, -2547243626485694309093770680025590588, 35994347046828757621806705902696276936278702102, -4513218104813627104768779562172445736435715220002242412, 59560962494213508162674167264470226970945042472540720083734037306]⟩

theorem UBC28_chk : UBC28.chk row0 = true := by
  -- kcost: 27 cells x 7 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC29 : Clu := ⟨463, 490, 2017749574449, 8348456440, 18, raw_ints% [50558614243, -102081398473327682882, 3671810164642415129986001175117, -8712940879890750624083188423237884963960, 260645129175255544185314073752823195285134783699675, -657807221352982170628704390499289959795497320059665099983242, 18359489228645233774159916689332629074674934795749498300479345356382737, -47862978888343412772450422701437195230972884259756463134698234496745289017330140, 1288575746271644439517232510866203244957177385577561263228664896637665772862626496728010455, -3426568023066593708266661582398464218920424569181716995499374005648779216855028445215724167837128062, 90260273671373433637829905945657128237893752134288478602084026389787693332065746835889325426387294961285991757, -243215083454867300376262672896090496499111051528925461951889825232592601899316453733474743284792684542735039153765295920, 6314679313986325768679808124391300540398748610539987184006259541267053236445701629905993097397283864213845379547422652384615205235, -17175590866425663251655104693962039347963613733019511974642149640887018581124916266183073777688859747245617119359300453131768409707940026482, 441419739599759943043206443380508813729483923333218750287306855153799690834367547687033028871004034897286092280780589487348571806328516010686165848777, -1208983356128732927345623762067265141669780254573111158258579491542542125417310123126328963659316454851189685510634057319196542762141824261946184274570038735300, 30839183161199104568843747708257314701776501865158376774196303433044832045913593104326309740203157187317239603142702290959294459973357482952338165900498309535037986104015, -84913297931494577597449276731811786422896526521342526816508838793974612981778480455462107503341186183228853656751353298548696583115589805949090341681894570867297659286888012270502, 2153629223453773085808350886316132662480903106260787465781310557679471973958507007741989311339163925137056289291159294290640390540342763055053607642849839507835499109145956799640644392449797]⟩

theorem UBC29_chk : UBC29.chk row0 = true := by
  -- kcost: 27 cells x 19 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC30 : Clu := ⟨490, 503, 2039773845270, 13675814381, 12, raw_ints% [44768540600, -106194799522978766113, 8549181130418524938558226722373, -24003971029077993720557789504247030240473, 1613266889135991634164097292808714229122563058264489, -4821203831726445905611406328470837140823790609682952807778177, 303214551169806151493511071475662535519233794807572965180882045660969153, -935251604406742087137821004806606204175749089902869763109074668531968616893936105, 56884680567765895379213695194451117828225049537722165176926113477701004665174038564610932713, -178728057066744520633870679167026609192068374705892151241410211779388590531581085879777440124521088401, 10661193736833989681260762707219834507628174842048479204589323174579002191360448756431020006041319726242151326353, -33890101581254846007147511923803504374429780714400115388593400592510661878146379510504570530128379309364870614597469025657, 1996883006894805944481529106685269228196887609816144876314309490797497737587696425731476142003028109278394106277700269542127613052537]⟩

theorem UBC30_chk : UBC30.chk row0 = true := by
  -- kcost: 13 cells x 13 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC31 : Clu := ⟨503, 516, 2073645426364, 20195766714, 10, raw_ints% [41413165430, -116442572354221280507, 17116032892113049898410518152349, -57160130043028498618885245822409606218889, 7020661948088203647612663704662033566502386200013233, -24978085236041961651336520917216236570426379120664139397741249, 2872434687240864779151304855581676764812332628681243375610719275880566777, -10550923498839904075162543448258656590649015049093709191721045556071926350748544401, 1173861596571928029307411541614848045044973327162465157720083118464063418025248998518885431041, -4392505736154106738241062052029606857995000370990559268525577826543231802035728531577825460851807266481, 479412041013058809034052927303817949534565571257425027165866396860198196240153945394954891690918048664271515033465]⟩

theorem UBC31_chk : UBC31.chk row0 = true := by
  -- kcost: 13 cells x 11 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC32 : Clu := ⟨516, 543, 2164441849477, 70600656399, 16, raw_ints% [80384548943, -1340386558332642531185, 415246074324685309279780098259022, -8153715109419711386030538483362655471541543, 2102207999258621247603504135591875346652600091430186496, -43943830300162062915538632868786985681841491193959223939158791509, 10570460644388563638774102196790987014245622318702849696595739426572450780118, -228414864476595073194139676942636912087268783767137753730310936956483067767208989096963, 52984903687512767862929693727301809622788227540616190118346872882292582662222880906486883596254444, -1168626730914224029611607940804315538239176439541980311180933077811130167932189338178619774953726387351375553, 265136259769037658011759716997524515629858820279051005645900887713761261588067670126990937299922975059396699467154616914, -5929127898389720514440984545809490356146392559220929217761181005729315637663395453081838838604137580269108270749304165688876387343, 1325368372602922476165838587630780586580290953496195953893339509845916943372613203501266530704020106636331525129278930343560804915035475520072, -29932665246824800663734746723761126611825828243980940515993336825376964698052812153537636481942352437026088659051109538801147656929489534361478772356717, 6620800144507537441031413163835013873587113315109770204290481092371815203507586708552398223250820764204254642062300457150859120970405049182083530334274462798514510, -150629850597021850673008442897308252108360473929045267403914219047868281840596900613567004305787570140970697368911683230261301700361149190508928202797058643678134064731688283, 33058393001894172099056739356302297592518427675421305473463782046026705731224228181561243811994129855139668012744559366531530244007047845349955470729891063525025040588774736737192330980]⟩

theorem UBC32_chk : UBC32.chk row0 = true := by
  -- kcost: 27 cells x 17 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC33 : Clu := ⟨543, 570, 2367034675763, 131992169887, 13, raw_ints% [76756917525, -2167651908617070612000, 1373644280810050088189305093541662, -45825225871412528216456122891219008669117920, 24211081994863251023001619331573427536316824888951238198, -860416429780291161002279100748212615508155444167041517966619819724, 424558238157390235339309661307841408197859092986613442732588031678688577034594, -15598915805496338422287463495199742750728269564183593802589122439680116982456332434523672, 7427528278885200039676075208986721213662946876280252658746828357094382584097724094427365661221653790, -278534028952560268810620549025065566909003534378714347025984334358490335740045359129653759552350387713699022788, 129777645529097258098426228822170916818604123268251076820614992661200168453204666696625481256671576365531590341388788916026, -4933922468921325274945270310788887948166028570139937828111069660668123006309511643572806416664095315032894247225562632368212206779024, 2265802982515130630749658447881622570394776696463425244329855510952186823656253436826631321513171307032933673597352914159032490744224587477113462, -86987209574387784447680600204570264654930695018323457906544967169717723996905450316078010035877091620194665460858500167664423254430610471793852991654395772]⟩

theorem UBC33_chk : UBC33.chk row0 = true := by
  -- kcost: 27 cells x 14 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC34 : Clu := ⟨570, 597, 2749470979403, 250444133753, 12, raw_ints% [75063233089, -4281767450908572403750, 4838084923233869904097276349328162, -325406466078982657498432972401900766526405188, 307038111848155176086812581248141316450250263681523592732, -21978247492661982465372224017217099587594666930894667353719456340342, 19385054043680451842129824841229026327467436872603967837600110675646203894637650, -1433736178305417112479751371752165609101421677636037989401919812953283319995162015265371640, 1221001460488270915299463812116772503530286829477230326605214481293208433132886030970443526600757237960, -92132684026177793088333594291705316425589206196411078740070080738597693242858427822903878843730270956222887263754, 76808591212194171576708706965287944059997831554826899780370764192310302565003768038262923604814179826774045563082230752435758, -5873964757125542679318784337310912731620641900006625691217376846557852057678945544455579756975205325194622868478095304186631184939818092, 4828008775997954942593221546786303246658407443635826018547318333127018354840589234483750209317118528622601374097799102782571819092472219254356218948]⟩

theorem UBC34_chk : UBC34.chk row0 = true := by
  -- kcost: 27 cells x 13 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC35 : Clu := ⟨597, 623, 3499503366729, 499588253574, 12, raw_ints% [70506856048, -9639529835825903622478, 18225646874404146593926010617614221, -2917957796223744880822728119277342539446865264, 4617907913586652345703711852815939068079326815947991093435, -784632472843927533776334767819395943841278303261968936745355099530430, 1162321197742458586526355300631141075066377155154533172200432949518891848261081121, -203738591216181238975322337242856081240677626527088052109507371028090291740353877324475359788, 291671265254916315211807888164882234588073065209286785525575434509082242698658509749391368015154896020519, -52107616604495518354532527244524550196610551906848928921882715720132009720749191787698437684546707207943332097110362, 73071926722119279874118644787057719590385906924219190367820868163505496921371917828592687311001094774702587690166255770585740461, -13221312620443482537717969763807778743386095068595327531060088548700266400351132821702351436975615542504171134033100806350348136420212443592, 18288526569515965404368508410954402403130692713102892503334015902685633378702135576001705087056855821579161616432782844886322276587449777436769064736563]⟩

theorem UBC35_chk : UBC35.chk row0 = true := by
  -- kcost: 26 cells x 13 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC36 : Clu := ⟨623, 650, 5236607213660, 1237515593358, 14, raw_ints% [62727010123, -32060889638430722616122, 102762795163375032210393019064450940, -60015066246714845265651426970384603937440467958, 161924257450330321796240580811024094264843833636457485038450, -99476403042856214903849051775239110382298745298849518022104384445164248, 251920032294204462938152074570332766523854020543012622933233582058005528177120933124, -158988513569182666255174084428734712998959353031544215815602347728746986875819416024707791355154, 389678953940991192955758193527400956137563919365708562953528981553886972613773753455886245950338548481380454, -250084481441071297876262732612847574469852551799521823956751124070648577042755732992216897335112432864026636817959928844, 600895491820576471404144100843090879472769303168412069880247608736677178881652865777417772596814946631490433191405841764630499608808, -390068860106448543516077651509614354871706148407024095897985278469574840895633899033763065370106828938724295255639666351446606654512194543829350, 924863432498161228399471402952488341212705044383598302100365438060295005055533094553208285732423602206211487972607728895078521594499144303945771031306013258, -605360934851443222716455276621258912596377044572790600157376086375488693340302963258761778556237266645199197346990060932131469627047586283777355316666407714933407230240, 1421768693603519695329500063108952717122467751142486033538541007303450216945342033108438659169645608426515798976923148293770840265884973051958896989264152387733314407646716876980492]⟩

theorem UBC36_chk : UBC36.chk row0 = true := by
  -- kcost: 27 cells x 15 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UBC37 : Clu := ⟨650, 704, 8677454408438, 2203331601420, 11, raw_ints% [24421557845, -40294243903177938729533, 125703222375849320683857500576873960, -241162160147644927991246175174914222902509870381, 624827211551300345941606865455602622572140992883452713930676, -1272054573193587419113134751843983455578612189327380948356378791542838549, 3074956153580600789532772112800390835141441127223814772587108823881410344905840173380, -6454583776695592068189575340064869967783664506565366723701735346097962884777077259788791176217213, 15069727153577853168570406414021141369452865874693129979489089474132885155790247848702084078996091852520754036, -32193795448468968012325692450681962035164141105831446802453630520675319931906195612745072336378454203477726423154609600085, 73689843434641362213932603098136956230893913602955680907617661768694234995870784009931688626812236492432856766105491121954644363954900, -159122749299391925684447765323589955434337526291779357442177043796329910456927615430512046538442146012159592304947850027159068178871498246641855645]⟩

theorem UBC37_chk : UBC37.chk row0 = true := by
  -- kcost: 54 cells x 12 moments, 0.3 s measured mean, 6 Nov
  decide +kernel

def UB : UnitD := ⟨999956799999, 399999, [UBC0, UBC1, UBC2, UBC3, UBC4, UBC5, UBC6, UBC7, UBC8, UBC9, UBC10, UBC11, UBC12, UBC13, UBC14, UBC15, UBC16, UBC17, UBC18], [UBC19], [UBC20, UBC21, UBC22, UBC23, UBC24, UBC25, UBC26, UBC27, UBC28, UBC29, UBC30, UBC31, UBC32, UBC33, UBC34, UBC35, UBC36, UBC37], 625, 627, false, false⟩

theorem UB_ok : UB.ok = true := by
  -- kcost: 38 pair checks, 3 near nodes, tile walks, 0.2 s measured, 6 Nov
  decide +kernel

theorem UB_fin : UB.fin = true := by
  -- kcost: 38 pair polynomials, 3 near polynomials, one sup bound, 2 s measured, 6 Nov
  decide +kernel

theorem UB_V : UB.V where
  ok := UB_ok
  fin := UB_fin
  h0 := List.forall_mem_cons.2 ⟨UBC0_chk, List.forall_mem_cons.2 ⟨UBC1_chk, List.forall_mem_cons.2 ⟨UBC2_chk, List.forall_mem_cons.2 ⟨UBC3_chk, List.forall_mem_cons.2 ⟨UBC4_chk, List.forall_mem_cons.2 ⟨UBC5_chk, List.forall_mem_cons.2 ⟨UBC6_chk, List.forall_mem_cons.2 ⟨UBC7_chk, List.forall_mem_cons.2 ⟨UBC8_chk, List.forall_mem_cons.2 ⟨UBC9_chk, List.forall_mem_cons.2 ⟨UBC10_chk, List.forall_mem_cons.2 ⟨UBC11_chk, List.forall_mem_cons.2 ⟨UBC12_chk, List.forall_mem_cons.2 ⟨UBC13_chk, List.forall_mem_cons.2 ⟨UBC14_chk, List.forall_mem_cons.2 ⟨UBC15_chk, List.forall_mem_cons.2 ⟨UBC16_chk, List.forall_mem_cons.2 ⟨UBC17_chk, List.forall_mem_cons.2 ⟨UBC18_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨UBC19_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨UBC20_chk, List.forall_mem_cons.2 ⟨UBC21_chk, List.forall_mem_cons.2 ⟨UBC22_chk, List.forall_mem_cons.2 ⟨UBC23_chk, List.forall_mem_cons.2 ⟨UBC24_chk, List.forall_mem_cons.2 ⟨UBC25_chk, List.forall_mem_cons.2 ⟨UBC26_chk, List.forall_mem_cons.2 ⟨UBC27_chk, List.forall_mem_cons.2 ⟨UBC28_chk, List.forall_mem_cons.2 ⟨UBC29_chk, List.forall_mem_cons.2 ⟨UBC30_chk, List.forall_mem_cons.2 ⟨UBC31_chk, List.forall_mem_cons.2 ⟨UBC32_chk, List.forall_mem_cons.2 ⟨UBC33_chk, List.forall_mem_cons.2 ⟨UBC34_chk, List.forall_mem_cons.2 ⟨UBC35_chk, List.forall_mem_cons.2 ⟨UBC36_chk, List.forall_mem_cons.2 ⟨UBC37_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem UB_cap : UnitCap (UB.M - UB.δ, UB.M + UB.δ) :=
  unit_cap_of UB_V (by decide +kernel) (by decide +kernel)

#print axioms freeColCap_of_units
#print axioms unit_cap_of
#print axioms unit_field
#print axioms UB_V
#print axioms UB_cap

end CatalanMeasure.GenD.Signed.RouteI.FreeColCert
