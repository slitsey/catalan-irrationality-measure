module

public import CatalanMeasure.Parametric.FullIntervalWeights

/-!
# Full-interval coefficient quadrature with original polynomial row values
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Polynomial.Chebyshev Finset OAI.InternalCatalan
open scoped BigOperators

noncomputable section

theorem rowCommonFactor_eval_ne_zero_of (P : Parameters) (N : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (rowCommonFactor P N).eval t ≠ 0 := by
  simp only [rowCommonFactor, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1.symm))

theorem filteredCatalanCoeff_full_weights {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0 < N) (hr : r < P.n N) {J : ℕ} (hJ : P.n N - P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ)
    (hτ0 : ∀ a, τ a ≠ 0) (hτ1 : ∀ a, τ a ≠ 1) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k : ℝ) =
      ∑ a, (realPoly (rowP P N r)).eval (τ a) * restrictedWeight P N k τ a := by
  rw [filteredCatalanCoeff_restricted_quadrature hP hN hr hJ hτ]
  apply sum_congr rfl
  intro a _
  have he : (realPoly (rowP P N r)).eval (τ a) =
      (rowCommonFactor P N).eval (τ a) * (realPoly (rowResidualP P N r)).eval (τ a) := by
    rw [rowP_common_factor hP hN hr]
    simp [realPoly, rowCommonFactor]
  have hn := rowCommonFactor_eval_ne_zero_of P N (hτ0 a) (hτ1 a)
  rw [he, restrictedWeight]
  field_simp

theorem chebX_even_ne_zero {J : ℕ} (hJ : Even J) (a : Fin J) :
    CatalanMeasure.chebX J a ≠ 0 := by
  have hm : 0 < J := by have := a.isLt; omega
  have hr : (T ℝ (J : ℤ)).eval (CatalanMeasure.chebX J a) = 0 := by
    rw [CatalanMeasure.T_eq_nodal hm, eval_mul, eval_C, eval_prod]
    apply mul_eq_zero_of_right
    apply prod_eq_zero (mem_univ a)
    simp
  intro hz
  rw [hz] at hr
  have hte := T_eval_zero_of_even (R := ℝ) (n := (J : ℤ)) (by exact_mod_cast hJ)
  rw [hte] at hr
  have hn : (((J : ℤ) / 2).negOnePow : ℤ) ≠ 0 := Units.ne_zero _
  exact hn (by exact_mod_cast hr)

theorem twenty_full_weight_formula {N r : ℕ} (hN : 0 < N) (hr : r < twenty.n N) (k : ℕ) :
    (filteredCatalanCoeffRat twenty N r k : ℝ) =
      ∑ a : Fin (18 * N), (realPoly (rowP twenty N r)).eval (CatalanMeasure.chebX (18 * N) a) *
        restrictedWeight twenty N k (CatalanMeasure.chebX (18 * N)) a := by
  apply filteredCatalanCoeff_full_weights twenty_admissible hN hr
    (by simp [Parameters.n, Parameters.g, twenty]; omega)
    (CatalanMeasure.chebX_injective _) _ _ k
  · intro a
    exact chebX_even_ne_zero ⟨9 * N, by omega⟩ a
  · intro a
    exact (CatalanMeasure.chebX_mem a).2.ne

theorem twenty_full_weight_joint_le (N k : ℕ) (a : Fin (18 * N)) :
    |(rowCommonFactor twenty N).eval (CatalanMeasure.chebX (18 * N) a)| *
        |restrictedWeight twenty N k (CatalanMeasure.chebX (18 * N)) a| ≤
      108000 * N * Real.exp (18 * N) := by
  have ha0 : CatalanMeasure.chebX (18 * N) a ≠ 0 := by
    exact chebX_even_ne_zero ⟨9 * N, by omega⟩ a
  have ha1 : CatalanMeasure.chebX (18 * N) a ≠ 1 := (CatalanMeasure.chebX_mem a).2.ne
  have hn := rowCommonFactor_eval_ne_zero_of twenty N ha0 ha1
  rw [restrictedWeight, abs_div, mul_comm, div_mul_cancel₀ _ (abs_ne_zero.mpr hn)]
  exact twenty_full_functional_le_exp N k a

end

end CatalanMeasure.Parametric
