module
public import CatalanCore.Li2.DecayCert.Lattice.Seed
@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators
namespace Polynomial
noncomputable section

-- The frozen S10 API uses the canonical constant-zero formal antiderivative.
def integral {K : Type*} [Field K] [CharZero K] (p : K[X]) : K[X] :=
  ∑ j ∈ Finset.range (p.natDegree+1),monomial (j+1) (p.coeff j/(j+1:ℕ))

theorem derivative_integral {K : Type*} [Field K] [CharZero K] (p : K[X]) :
    p.integral.derivative=p := by
  rw [integral,derivative_sum]
  calc
    _ = ∑ j ∈ Finset.range (p.natDegree+1),monomial j (p.coeff j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [derivative_monomial_succ]
      congr 1
      have hj0 : ((j+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
    _ = p := p.as_sum_range.symm

theorem integral_eval_zero {K : Type*} [Field K] [CharZero K] (p : K[X]) :
    p.integral.eval 0=0 := by
  rw [integral,Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  simp [Polynomial.eval_monomial]

theorem integral_eval_hasDerivAt (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun t => p.integral.eval t) (p.eval x) x := by
  simpa only [derivative_integral] using p.integral.hasDerivAt x
#print axioms derivative_integral
#print axioms integral_eval_zero
#print axioms integral_eval_hasDerivAt
end
end Polynomial
