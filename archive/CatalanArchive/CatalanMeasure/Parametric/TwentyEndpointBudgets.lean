module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyBudgets
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

/-- The interpolated first-case certificate has the common global energy target. -/
theorem twenty_first_endpoint_budget {t : ℝ} (ht : 0 ≤ t) :
    -(1/5:ℝ)*Real.log 2+
      (1-t)*(twentyNorm10+(1-t)*twentyFields10+t*twentyFixed10)+
      t*(twentyNorm11+(1-t)*twentyFields11+t*twentyFixed11)+(2*t-t^2)*Real.log 2 ≤
      -twentyDualTarget+Real.log 2/2+(43/10)*t :=by
  have hc :=twenty_budget_checks
  have hd : twentyNorm10+twentyFields10 ≤ -twentyDualTarget+(7/10)*Real.log 2-8/125 :=by
    linarith only [hc.1]
  have hh :=first_population_endpoint_le (K0 :=twentyNorm10) (K1 :=twentyNorm11)
    (B0 :=twentyFields10) (B1 :=twentyFields11) (Y0 :=twentyFixed10) (Y1 :=twentyFixed11)
    (U :=-twentyDualTarget+(7/10)*Real.log 2) ht hd
    (by change twentyFirstCost ≤ 481/100;exact hc.2.2.1)
    (by change twentyFirstQuadratic ≤ -(53/50);exact hc.2.2.2.1)
  linarith only [hh]

theorem twenty_second_endpoint_budget {t : ℝ} (ht : 0 ≤ t) :
    -(1/5:ℝ)*Real.log 2+
      (1-t)*(twentyNorm20+(1-t)*twentyFields20+t*(-1/5))+
      t*(twentyNorm21+(1-t)*twentyFields21+t*(-1/5))+(2*t-t^2)*Real.log 2 ≤
      -twentyDualTarget+Real.log 2/2+(43/10)*t :=by
  have hc :=twenty_budget_checks
  have hm :=second_population_missing_mass_le hc.2.2.2.2.1 hc.2.2.2.2.2 ht
  calc
    _ = -(1/5:ℝ)*Real.log 2+twentyNorm20+twentyFields20+
        t*twentySecondCost+t^2*twentySecondQuadratic :=by
      unfold twentySecondCost twentySecondQuadratic
      ring
    _ ≤ _ :=by nlinarith only [hm,hc.2.1]

end
end CatalanMeasure.Parametric
