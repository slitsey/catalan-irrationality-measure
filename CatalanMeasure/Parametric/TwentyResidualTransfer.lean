module
public import CatalanMeasure.Cert.ResidualField
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan CatalanMeasure.Cert Set
noncomputable section

def twentyResidualTwo (cs : List ℤ) (tail : List TailQ) (x : ℝ) : ℝ :=
  -(2/5:ℝ)*Real.log 2-(9/10:ℝ)*Real.log (1+x^2)-2*barrierTrialT (trialSeq cs tail) x

/-- An old-form residual certificate transfers to the actual 20-row fixed field. -/
theorem twentyResidualTwo_le {cs : List ℤ} {tail : List TailQ} {x : ℝ}
    (hx : x ∈ Icc (-1:ℝ) 0) (h : residualTwoField cs tail x ≤ -(101/500:ℝ)) :
    twentyResidualTwo cs tail x ≤ -(1/5:ℝ) :=by
  have hden : 0<1+x^2 :=by positivity
  have hsq : x^2 ≤ 1 :=by nlinarith only [hx.1,hx.2]
  have hl : Real.log (1+x^2) ≤ Real.log 2 :=Real.log_le_log hden (by linarith only [hsq])
  have hu :=Real.log_two_lt_d9
  unfold twentyResidualTwo residualTwoField at *
  norm_num at hu
  linarith only [h,hl,hu]

end
end CatalanMeasure.Parametric
