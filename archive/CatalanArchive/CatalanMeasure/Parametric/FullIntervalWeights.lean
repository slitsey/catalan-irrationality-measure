module

public import CatalanArchive.CatalanMeasure.Parametric.FullIntervalQuadrature
public import CatalanArchive.CatalanMeasure.Parametric.TwentyRestrictedWeights

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Finset OAI.InternalCatalan

noncomputable section

theorem twenty_full_common_basis_coeff_zero (N : ℕ) (a : Fin (18 * N)) (i : ℕ)
    (hi : twenty.H N ≤ i) :
    (rowCommonFactor twenty N *
      quadBasis (CatalanMeasure.chebX (18 * N)) a).coeff i = 0 := by
  have hf := rowCommonFactor_natDegree_le twenty N
  have hb := quadBasis_natDegree_le (CatalanMeasure.chebX_injective (18 * N)) a
  have hd : (rowCommonFactor twenty N *
      quadBasis (CatalanMeasure.chebX (18 * N)) a).natDegree ≤
      (rowCommonFactor twenty N).natDegree +
      (quadBasis (CatalanMeasure.chebX (18 * N)) a).natDegree := natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  rw [twenty_A] at hf
  change (rowCommonFactor twenty N).natDegree ≤ 8 * N + 1 * N at hf
  rw [twenty_H] at hi
  have hN : 0 < N := by have := a.isLt; omega
  omega

/-- A uniform bound for the actual filtered coefficient functional on the
full-interval residual interpolation basis. -/
theorem twenty_full_functional_le (N k : ℕ) (a : Fin (18 * N)) :
    |polynomialFunctional twenty N k (rowCommonFactor twenty N *
      quadBasis (CatalanMeasure.chebX (18 * N)) a)| ≤
      108000 * N * (60000000 : ℝ) ^ N := by
  have hh := polynomialFunctional_common_factor_le twenty N k
    (quadBasis (CatalanMeasure.chebX (18 * N)) a)
    (twenty_full_common_basis_coeff_zero N a)
    (radius := (TwentyCircle.twentyRadius : ℝ)) (B := 1000 * (60000000 : ℝ) ^ N)
    (by norm_num [TwentyCircle.twentyRadius]) (fun z hz => by
      simpa only [Parameters.h, Parameters.q, twenty,
        show 1 * N + 1 * N = 2 * N by ring] using twenty_full_filtered_basis_le N a z hz)
  rw [twenty_H] at hh
  convert hh using 1 <;> push_cast <;> ring

theorem twenty_full_functional_le_exp (N k : ℕ) (a : Fin (18 * N)) :
    |polynomialFunctional twenty N k (rowCommonFactor twenty N *
      quadBasis (CatalanMeasure.chebX (18 * N)) a)| ≤
      108000 * N * Real.exp (18 * N) := by
  have hK : (60000000 : ℝ) ^ N ≤ Real.exp (18 * N) := by
    calc
      _ ≤ Real.exp 18 ^ N :=
        pow_le_pow_left₀ (by norm_num) fullIntervalCircleK_le_exp N
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (twenty_full_functional_le N k a).trans
    (mul_le_mul_of_nonneg_left hK (by positivity))

end

end CatalanMeasure.Parametric
