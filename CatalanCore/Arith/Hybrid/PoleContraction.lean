module
public import CatalanCore.Arith.Hybrid.LoewnerMoment
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid

/-- Exact cancellation of the apparent pole. The remaining error has an explicit
factor eps and only unit denominators in the valuation-ring application. -/
theorem contracted_pole_exact {K ι : Type*} [Field K] [Fintype ι]
    (v f t : ι→K) (n eps d : K) (hn : n≠0) (heps : eps≠0) (hd : d≠0)
    (hshift : ∀i j,d+eps*(t j-t i)≠0) :
    (∑i,∑j,v i*v j*(f i-f j)/(n*eps*(d+eps*(t j-t i)))) =
      -2*((∑i,v i*f i)*(∑i,v i*t i)-(∑i,v i)*(∑i,v i*f i*t i))/(n*d^2)
      +eps*(∑i,∑j,v i*v j*(f i-f j)*(t j-t i)^2/
        (n*d^2*(d+eps*(t j-t i)))) := by
  have point (i j) : v i*v j*(f i-f j)/(n*eps*(d+eps*(t j-t i))) =
      v i*v j*(f i-f j)/(n*eps*d)
      -v i*v j*(f i-f j)*(t j-t i)/(n*d^2)
      +eps*(v i*v j*(f i-f j)*(t j-t i)^2/(n*d^2*(d+eps*(t j-t i)))) := by
    field_simp [hn,heps,hd,hshift i j]
    <;> ring
  have zeroSum : (∑i,∑j,v i*v j*(f i-f j))=0 := by
    have H : (∑i,∑j,v i*v j*f i)=(∑i,∑j,v i*v j*f j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [H,sub_self]
  simp_rw [point]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.sum_div,←Finset.mul_sum]
  rw [zeroSum,zero_div,zero_sub,difference_moment_sum]
  ring

#print axioms contracted_pole_exact
end CatalanCore.Arith.Hybrid
