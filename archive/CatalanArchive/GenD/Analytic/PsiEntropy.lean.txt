module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import CatalanMeasure.GenD.Analytic.WeightedAtom

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Real Set
noncomputable section

/-! Continuum entropy selector (plan row C2). For `0 < r` and `0 ≤ k ≤ 1`,
`H(k) - k log r ≤ log (1 + 1/r)` (log-concavity / Jensen), so one price check at the
radius replaces the finite κ-cover of `Analytic.PsiSelector`. -/

theorem entropy_sub_mul_log_le (r k : ℝ) (hr : 0 < r) (hk : k ∈ Icc (0 : ℝ) 1) :
    binEntropy k - k * Real.log r ≤ Real.log (1 + 1 / r) := by
  rcases hk with ⟨hk0, hk1⟩
  by_cases h0 : k = 0
  · subst k
    simp only [binEntropy_zero, zero_mul, sub_zero]
    exact Real.log_nonneg (by linarith [one_div_pos.mpr hr] : (1 : ℝ) ≤ 1 + 1 / r)
  by_cases h1 : k = 1
  · subst k
    simp only [binEntropy_one, one_mul, zero_sub]
    rw [← Real.log_inv]
    exact Real.log_le_log (inv_pos.mpr hr) (by simp only [one_div]; linarith)
  have kp : 0 < k := lt_of_le_of_ne hk0 (Ne.symm h0)
  have km : 0 < 1 - k := sub_pos.mpr (lt_of_le_of_ne hk1 h1)
  have hJ := strictConcaveOn_log_Ioi.concaveOn.2
    (show 0 < 1 / (k * r) by positivity)
    (show 0 < 1 / (1 - k) by positivity)
    kp.le km.le (by ring : k + (1 - k) = 1)
  have harg : k * (1 / (k * r)) + (1 - k) * (1 / (1 - k)) = 1 + 1 / r := by
    field_simp
    <;> ring
  simp only [smul_eq_mul] at hJ
  rw [harg] at hJ
  simp only [one_div, Real.log_inv, Real.log_mul kp.ne' hr.ne'] at hJ
  simp only [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def, one_div]
  nlinarith [hJ]

/-- The clipped entropy `binomRate` satisfies the same linear-in-`k` bound for `r ≤ 1`. -/
theorem binomRate_sub_mul_log_le (r k : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hk : k ∈ Icc (0 : ℝ) 1) :
    binomRate k - k * Real.log r ≤ Real.log (1 + 1 / r) := by
  unfold binomRate
  split_ifs with h
  · exact entropy_sub_mul_log_le r k hr hk
  · have hhalf := entropy_sub_mul_log_le r (2⁻¹) hr (by norm_num)
    rw [binEntropy_two_inv] at hhalf
    have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    have hm : (2⁻¹ : ℝ) * Real.log r ≤ k * Real.log r :=
      mul_le_mul_of_nonpos_right (by linarith) hl
    linarith

/-- Continuum affine circle/entropy selector: one price check at the radius covers every
`κ ∈ [0,1]`, with the exact conclusion of `finite_affine_circle_selector`. -/
theorem affine_binomRate_continuum (r shift n C Ψ : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hn : 0 ≤ n)
    (hprice : shift * Real.log r + C + n * Real.log (1 + 1 / r) ≤ Ψ) :
    ∀ κ ∈ Icc (0 : ℝ) 1,
      (shift - n * κ) * Real.log r + C + n * binomRate κ ≤ Ψ := by
  intro k hk
  have h := mul_le_mul_of_nonneg_left (binomRate_sub_mul_log_le r k hr hr1 hk) hn
  nlinarith

/-- Same, with the price given through any upper bound `L` for `log (1 + 1/r)`. -/
theorem affine_binomRate_continuum_of_log_le (r shift n C L Ψ : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (hn : 0 ≤ n) (hL : Real.log (1 + 1 / r) ≤ L)
    (hprice : shift * Real.log r + C + n * L ≤ Ψ) :
    ∀ κ ∈ Icc (0 : ℝ) 1,
      (shift - n * κ) * Real.log r + C + n * binomRate κ ≤ Ψ :=
  affine_binomRate_continuum r shift n C Ψ hr hr1 hn
    (by nlinarith [mul_le_mul_of_nonneg_left hL hn])

/-- Supremum form: if the radius-wise price holds on a set of radii, the selector holds
at every radius of the set and every `κ`. -/
theorem affine_binomRate_continuum_on {R : Set ℝ} (shift n C Ψ : ℝ)
    (hR : ∀ r ∈ R, 0 < r ∧ r ≤ 1) (hn : 0 ≤ n)
    (hprice : ∀ r ∈ R, shift * Real.log r + C + n * Real.log (1 + 1 / r) ≤ Ψ) :
    ∀ r ∈ R, ∀ κ ∈ Icc (0 : ℝ) 1,
      (shift - n * κ) * Real.log r + C + n * binomRate κ ≤ Ψ :=
  fun r hr => affine_binomRate_continuum r shift n C Ψ (hR r hr).1 (hR r hr).2 hn (hprice r hr)

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.entropy_sub_mul_log_le
#print axioms CatalanMeasure.GenD.Analytic.binomRate_sub_mul_log_le
#print axioms CatalanMeasure.GenD.Analytic.affine_binomRate_continuum
#print axioms CatalanMeasure.GenD.Analytic.affine_binomRate_continuum_of_log_le
#print axioms CatalanMeasure.GenD.Analytic.affine_binomRate_continuum_on
