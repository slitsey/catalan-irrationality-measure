module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CatalanMeasure.Parametric.TwoAdicCoefficientEntryBounds
public import CatalanArchive.CatalanMeasure.Parametric.TwentyTwoAdicSelectors
public import CatalanMeasure.Parametric.TwentyParameters
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem twentyRawCoefficientTerm_eq_det (z : ℚ) (N : ℕ)
    (c : Fin (twenty.n N) → ↥(Finset.Ico (twenty.b N) (twenty.L N)))
    (τ : Fin (twenty.n N) → Fin 3)
    (u : ∀ k : Fin (twenty.n N), paramRawCoefficientIndex twenty N (τ k)) :
    (∏ k : Fin (twenty.n N), paramRawCoefficientScalar twenty z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor twenty N c τ u =
      Matrix.det (Matrix.of fun r k : Fin (twenty.n N) =>
        paramRawCoefficientVector twenty N r.val (c k).val (τ k) (u k).val *
          paramRawCoefficientScalar twenty z N (c k).val (τ k) (u k).val) := by
  classical
  simp only [paramRawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  ring

private theorem prod_two_zpow_neg {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (∏ k, (2 : ℝ) ^ (-v k)) = (2 : ℝ) ^ (-(∑ k, v k)) := by
  classical
  calc
    _ = ∏ k, (2 : ℝ) ^ (((-v k) : ℤ) : ℝ) := by
      simp only [Real.rpow_intCast]
    _ = (2 : ℝ) ^ (∑ k, (((-v k) : ℤ) : ℝ)) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ (((-(∑ k, v k)) : ℤ) : ℝ) := by
      simp only [Int.cast_neg, Int.cast_sum, Finset.sum_neg_distrib]
    _ = _ := Real.rpow_intCast _ _

theorem twentyRawCoefficientTerm_norm_le_zpow (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (twenty.n N) → ↥(Finset.Ico (twenty.b N) (twenty.L N)))
    (τ : Fin (twenty.n N) → Fin 3)
    (u : ∀ k : Fin (twenty.n N), paramRawCoefficientIndex twenty N (τ k)) :
    ‖(∏ k : Fin (twenty.n N), paramRawCoefficientScalar twenty z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor twenty N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ (-(∑ k : Fin (twenty.n N),
          if τ k = 0 then (twenty.C N : ℤ)
          else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (twenty.H N : ℤ)
          else ((u k).val : ℤ))) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [twentyRawCoefficientTerm_eq_det]
  calc
    _ ≤ ∏ k : Fin (twenty.n N),
        (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(if τ k = 0 then (twenty.C N : ℤ)
            else if τ k = 1 then 2 * ((u k).val : ℤ) + ((c k).val : ℤ) - (twenty.H N : ℤ)
            else ((u k).val : ℤ))) := by
      apply padic_two_det_norm_le_prod_column
      · intro k
        positivity
      · intro r k
        exact paramRawCoefficientEntry_norm_le twenty twenty_admissible z hN
          (Finset.mem_Ico.mp (c k).property).2 (τ k) (u k)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, prod_two_zpow_neg]

set_option backward.isDefEq.respectTransparency false in
theorem twentyRawCoefficientTerm_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (twenty.n N) → ↥(Finset.Ico (twenty.b N) (twenty.L N))) (hc : Function.Injective c)
    (τ : Fin (twenty.n N) → Fin 3)
    (u : ∀ k : Fin (twenty.n N), paramRawCoefficientIndex twenty N (τ k)) :
    ‖(∏ k : Fin (twenty.n N), paramRawCoefficientScalar twenty z N (c k).val (τ k) (u k).val) *
        paramRawCoefficientMinor twenty N c τ u‖ ≤
      (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) := by
  have hF := discrepancyNormFactor_nonneg z
  by_cases hz : paramRawCoefficientMinor twenty N c τ u = 0
  · rw [hz, mul_zero, norm_zero]
    positivity
  have hj : Function.Injective (fun k => (c k).val) := by
    intro i j hij
    exact hc (Subtype.ext hij)
  have hp := twenty_two_adic_selector_zpow_le N τ (fun k => (u k).val) (fun k => (c k).val)
    (paramRawCoefficientMinor_exception_injOn twenty N c τ u hz)
    (paramRawCoefficientMinor_boundary_injOn twenty N c τ u hz) hj
    (fun k => (Finset.mem_Ico.mp (c k).property).1)
  exact (twentyRawCoefficientTerm_norm_le_zpow z hN c τ u).trans
    (mul_le_mul_of_nonneg_left (by
      convert hp using 1 <;>
        simp only [twenty_C,twenty_H,Nat.cast_mul,Nat.cast_ofNat] <;> rfl) (by positivity))

theorem twentyRawColumnMinor_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (twenty.n N) → ↥(Finset.Ico (twenty.b N) (twenty.L N))) (hc : Function.Injective c)
    (τ : Fin (twenty.n N) → Fin 3) :
    ‖Matrix.det (Matrix.of fun r k : Fin (twenty.n N) =>
      paramRawColumnTerm twenty z N r.val (c k).val (τ k))‖ ≤
      (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramRawColumnMinor_coefficient_expansion]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro u hu
  exact twentyRawCoefficientTerm_norm_le z hN c hc τ u

theorem twentyRawMinorRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N)
    (c : Fin (twenty.n N) → ↥(Finset.Ico (twenty.b N) (twenty.L N))) (hc : Function.Injective c) :
    ‖(paramRawMinorRat twenty z N c : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramRawMinorRat_two_adic_column_expansion twenty twenty_admissible z hN c]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro τ hτ
  exact twentyRawColumnMinor_norm_le z hN c hc τ

theorem twentyDeterminantRat_two_adic_norm_le (z : ℚ) {N : ℕ} (hN : 0 < N) :
    ‖(determinantRat twenty z N : ℚ_[2])‖ ≤
      (8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) := by
  classical
  have hF := discrepancyNormFactor_nonneg z
  rw [paramDeterminantRat_eq_sum_raw_minors]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro c hc
  rw [norm_mul]
  calc
    _ ≤ 1 * ((8 * discrepancyNormFactor z * (twenty.H N : ℝ) ^ 2) ^ twenty.n N *
        (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N)) :=
      mul_le_mul (Padic.norm_int_le_one _)
        (twentyRawMinorRat_two_adic_norm_le z hN c (Finset.mem_filter.mp hc).2)
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _


end
end CatalanMeasure.Parametric
