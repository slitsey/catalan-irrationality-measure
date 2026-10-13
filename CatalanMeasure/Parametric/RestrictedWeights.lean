module
public import CatalanMeasure.Parametric.PolynomialFunctional
public import CatalanMeasure.Parametric.RadiusQuadrature
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset
noncomputable section

theorem quadBasis_natDegree_le {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (a : Fin J) :
    (OAI.InternalCatalan.quadBasis τ a).natDegree ≤ J-1 := by
  have hh := Lagrange.natDegree_basis (s := (univ:Finset (Fin J))) (v := τ)
    (fun x _ y _ hxy => hτ hxy) (mem_univ a)
  simpa [OAI.InternalCatalan.quadBasis] using hh.le

theorem rowCommonFactor_natDegree_le (P : Parameters) (N : ℕ) :
    (rowCommonFactor P N).natDegree ≤ P.A N+P.h N := by
  have hb : (1-X:ℝ[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le (1:ℝ[X]) X
  have hp : ((1-X:ℝ[X])^(P.h N)).natDegree ≤ P.h N*(1-X:ℝ[X]).natDegree := natDegree_pow_le
  unfold rowCommonFactor
  have hh : ((X^(P.A N):ℝ[X])*((1-X)^(P.h N))).natDegree ≤
      (X^(P.A N):ℝ[X]).natDegree+((1-X:ℝ[X])^(P.h N)).natDegree := natDegree_mul_le
  rw [natDegree_X_pow] at hh
  nlinarith

theorem proposed_common_basis_coeff_zero (N : ℕ) (a : Fin (89*N)) (i : ℕ)
    (hi : proposed.H N ≤ i) :
    (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).coeff i=0 := by
  have hf := rowCommonFactor_natDegree_le proposed N
  have hb := quadBasis_natDegree_le (CatalanMeasure.chebNode_injective (89*N)) a
  have hd : (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).natDegree ≤
      (rowCommonFactor proposed N).natDegree +
      (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).natDegree := natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  rw [proposed_A] at hf
  change (rowCommonFactor proposed N).natDegree ≤ 36*N+5*N at hf
  rw [proposed_H] at hi
  have hN : 0<N := by have := a.isLt; omega
  omega

theorem proposed_restricted_functional_le (N k : ℕ) (a : Fin (89*N)) :
    |polynomialFunctional proposed N k (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a)| ≤
      260000*N*(residualCircleK:ℝ)^N := by
  have hh := polynomialFunctional_common_factor_le proposed N k
    (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a)
    (proposed_common_basis_coeff_zero N a)
    (radius := (residualRadius:ℝ)) (B := 500*(residualCircleK:ℝ)^N)
    (by norm_num [residualRadius]) (fun z hz => by
      simpa only [Parameters.h,Parameters.q,proposed,show 5*N+7*N=12*N by ring] using
        norm_restricted_filtered_basis_le N a z hz)
  rw [proposed_H] at hh
  convert hh using 1 <;> push_cast <;> ring

def restrictedWeight (P : Parameters) (N k : ℕ) {J : ℕ} (τ : Fin J → ℝ) (a : Fin J) : ℝ :=
  polynomialFunctional P N k (rowCommonFactor P N * OAI.InternalCatalan.quadBasis τ a) /
    (rowCommonFactor P N).eval (τ a)

theorem rowCommonFactor_eval_ne_zero (P : Parameters) (N : ℕ) {t : ℝ} (ht : t<0) :
    (rowCommonFactor P N).eval t ≠ 0 := by
  simp only [rowCommonFactor,eval_mul,eval_pow,eval_X,eval_sub,eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht.ne) (pow_ne_zero _ (by linarith))

/-- The weights must be bounded jointly with the common-factor node weight. -/
theorem proposed_restrictedWeight_joint_le (N k : ℕ) (a : Fin (89*N)) :
    |(rowCommonFactor proposed N).eval (CatalanMeasure.chebNode (89*N) a)| *
      |restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a| ≤
      260000*N*(residualCircleK:ℝ)^N := by
  have hn := rowCommonFactor_eval_ne_zero proposed N (CatalanMeasure.chebNode_mem a).2
  rw [restrictedWeight,abs_div,mul_comm,div_mul_cancel₀ _ (abs_ne_zero.mpr hn)]
  exact proposed_restricted_functional_le N k a

/-- The reduced quadrature formula uses actual row values, with the shared factor
in the denominator of each weight. This is the form required in determinants. -/
theorem filteredCatalanCoeff_restricted_weights {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0<N) (hr : r<P.n N) {J : ℕ} (hJ : P.n N-P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) (hneg : ∀ a, τ a<0) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k:ℝ) =
      ∑ a, (OAI.InternalCatalan.realPoly (rowP P N r)).eval (τ a) *
        restrictedWeight P N k τ a := by
  rw [filteredCatalanCoeff_restricted_quadrature hP hN hr hJ hτ]
  apply sum_congr rfl
  intro a _
  have he : (OAI.InternalCatalan.realPoly (rowP P N r)).eval (τ a) =
      (rowCommonFactor P N).eval (τ a) *
      (OAI.InternalCatalan.realPoly (rowResidualP P N r)).eval (τ a) := by
    rw [rowP_common_factor hP hN hr]
    simp [OAI.InternalCatalan.realPoly,rowCommonFactor]
  have hn := rowCommonFactor_eval_ne_zero P N (hneg a)
  rw [he,restrictedWeight]
  field_simp

end
end CatalanMeasure.Parametric
