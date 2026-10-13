module
public import CatalanMeasure.Parametric.TwentyTrialFields
public import CatalanMeasure.Parametric.TwentyResidualTransfer
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan CatalanMeasure.Cert
noncomputable section

/-- The residual certificate controls the actual fixed-node field after the
    common factor is canceled, at every positive scale. -/
theorem twenty_fixed_two_after_common {N : ℕ} (hN : 0<N) (cs : List ℤ) (tail : List TailQ)
    {x : ℝ} (hx : x<0) :
    paramPopulationRowField twenty N 2 x-2*barrierTrialT (trialSeq cs tail) x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ)=
      twentyResidualTwo cs tail x :=by
  have hh :=paramPopulationRowField_sub_common twenty_admissible hN 2 hx
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  rw [twenty_A] at hh
  change paramPopulationRowField twenty N 2 x-
    Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ)=
      -((8*N:ℕ):ℝ)/((20*N:ℕ):ℝ)*Real.log 2-
        ((2:ℝ)/2-((2*N:ℕ):ℝ)/((20*N:ℕ):ℝ))*Real.log (1+x^2) at hh
  have hcommon : paramPopulationRowField twenty N 2 x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ)=
      -(2/5:ℝ)*Real.log 2-(9/10:ℝ)*Real.log (1+x^2) :=by
    rw [hh]
    push_cast
    field_simp
    ring
  unfold twentyResidualTwo
  linarith only [hcommon]

end
end CatalanMeasure.Parametric
