module
public import CatalanMeasure.Parametric.RestrictedQuadrature
public import CatalanMeasure.QuadCircle
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset
noncomputable section

/-- The actual filtered Catalan coefficient, as a linear functional on row polynomials. -/
def polynomialFunctional (P : Parameters) (N k : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  ∑ v ∈ range (P.q N+1), ((-1:ℝ)^v*((P.q N).choose v:ℝ)) •
    ∑ i ∈ range (P.H N),
      (4*(OAI.InternalCatalan.centralCoeffKernel ((i:ℤ)-((P.b N+k+v:ℕ):ℤ)):ℝ)) •
        Polynomial.lcoeff ℝ i

theorem polynomialFunctional_apply (P : Parameters) (N k : ℕ) (Q : ℝ[X]) :
    polynomialFunctional P N k Q =
      ∑ v ∈ range (P.q N+1), ((-1:ℝ)^v*((P.q N).choose v:ℝ)) *
        ∑ i ∈ range (P.H N), Q.coeff i *
          (4*(OAI.InternalCatalan.centralCoeffKernel ((i:ℤ)-((P.b N+k+v:ℕ):ℤ)):ℝ)) := by
  simp [polynomialFunctional,mul_comm]

theorem filteredCatalanCoeff_as_functional (P : Parameters) (N r k : ℕ) :
    (filteredCatalanCoeffRat P N r k:ℝ) =
      polynomialFunctional P N k (OAI.InternalCatalan.realPoly (rowP P N r)) := by
  rw [polynomialFunctional_apply]
  unfold filteredCatalanCoeffRat rawCatalanCoeffRat filterCoeffRat
  push_cast
  simp only [OAI.InternalCatalan.realPoly_coeff]

theorem polynomialFunctional_eq_coeff (P : Parameters) (N k : ℕ) (Q : ℝ[X])
    (hdeg : ∀ i, P.H N ≤ i → Q.coeff i=0) :
    polynomialFunctional P N k Q =
      4*∑ d ∈ range (P.H N), (OAI.InternalCatalan.centralCoeffKernel (d:ℤ):ℝ) *
        (Q*(X-1)^(P.q N)).coeff (P.b N+k+d+P.q N) := by
  rw [polynomialFunctional_apply]
  have hstep : ∀ v ∈ range (P.q N+1), ((-1:ℝ)^v*((P.q N).choose v:ℝ)) *
      ∑ i ∈ range (P.H N), Q.coeff i *
        (4*(OAI.InternalCatalan.centralCoeffKernel ((i:ℤ)-((P.b N+k+v:ℕ):ℤ)):ℝ)) =
      4*∑ d ∈ range (P.H N), ((-1:ℝ)^v*((P.q N).choose v:ℝ)) *
        Q.coeff (P.b N+k+v+d) * (OAI.InternalCatalan.centralCoeffKernel (d:ℤ):ℝ) := by
    intro v _
    have hh := OAI.InternalCatalan.sum_shift_kernel (H := P.H N) (m := P.b N+k+v)
      (fun i => Q.coeff i) hdeg
    simp_rw [mul_left_comm _ (4:ℝ),← mul_sum,hh,mul_sum]
    ring_nf
  rw [sum_congr rfl hstep,← mul_sum,sum_comm]
  congr 1
  apply sum_congr rfl
  intro d _
  rw [show P.b N+k+d+P.q N=(P.b N+k+d)+P.q N by ring,
    OAI.InternalCatalan.coeff_mul_X_sub_one_pow,mul_sum]
  apply sum_congr rfl
  intro v _
  rw [show P.b N+k+d+v=P.b N+k+v+d by ring]
  ring

theorem filteredCatalanCoeff_restricted_quadrature {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0<N) (hr : r<P.n N) {J : ℕ} (hJ : P.n N-P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k:ℝ) =
      ∑ a, (OAI.InternalCatalan.realPoly (rowResidualP P N r)).eval (τ a) *
        polynomialFunctional P N k (rowCommonFactor P N*OAI.InternalCatalan.quadBasis τ a) := by
  rw [filteredCatalanCoeff_as_functional,rowP_restricted_interpolate hP hN hr hJ hτ]
  rw [map_sum]
  apply sum_congr rfl
  intro a _
  rw [← smul_eq_C_mul,LinearMap.map_smul]
  rfl

end
end CatalanMeasure.Parametric
