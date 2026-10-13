module
public import CatalanMeasure.Parametric.TwentyCertifiedFields
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

theorem twenty_fixed_one_le {N : ℕ} (hN : 0<N) {lambda x : ℝ}
    (hlambda : 0 ≤ lambda) (hx : x<0) :
    paramPopulationRowField twenty N 1 x+lambda*paramCaseField twenty N x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ) ≤
      -(2/5:ℝ)*Real.log 2+lambda/5 :=by
  rw [paramFixedOne_sub_common twenty_admissible hN lambda hx]
  have hh :=paramResidualFixedOne_le twenty_admissible hN hlambda x
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  have he : -(twenty.A N:ℝ)/(twenty.n N:ℝ)*Real.log 2+
      lambda*2*(twenty.g N:ℝ)/(twenty.n N:ℝ)=-(2/5:ℝ)*Real.log 2+lambda/5 :=by
    rw [twenty_A]
    change -((8*N:ℕ):ℝ)/((20*N:ℕ):ℝ)*Real.log 2+
      lambda*2*((2*N:ℕ):ℝ)/((20*N:ℕ):ℝ)=_
    push_cast
    field_simp
    ring
  exact hh.trans_eq he

namespace TwentyCertified
theorem fixed10_bound {N : ℕ} (hN : 0<N) {x : ℝ} (hx : x<0) :
    paramPopulationRowField twenty N 1 x+(lambda10:ℝ)*paramCaseField twenty N x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ) ≤ twentyFixed10 :=by
  have hh :=twenty_fixed_one_le hN (lambda :=(lambda10:ℝ)) (by norm_num [lambda10]) hx
  convert hh using 1 <;> norm_num [twentyFixed10,lambda10] <;> ring

theorem fixed11_bound {N : ℕ} (hN : 0<N) {x : ℝ} (hx : x<0) :
    paramPopulationRowField twenty N 1 x+(lambda11:ℝ)*paramCaseField twenty N x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ) ≤ twentyFixed11 :=by
  have hh :=twenty_fixed_one_le hN (lambda :=(lambda11:ℝ)) (by norm_num [lambda11]) hx
  convert hh using 1 <;> norm_num [twentyFixed11,lambda11] <;> ring
end TwentyCertified

end
end CatalanMeasure.Parametric
