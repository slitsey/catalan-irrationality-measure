import CatalanCore.Uniform.Bank.Lambda.Final
import CatalanCore.Uniform.Bank.Lambda.Frame
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform

/-- Conditional assembly on the new family. Content and decay remain explicit providers. -/
theorem lambda_measure (sgn : Bool)
    (hS : HasScaledContent
      ((FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)).restrictAdm
        (fun i => i.1 % 2 = 0)) FL.scale LamL)
    (hD : HasScaledDecay
      (FL.family (lambdaFrame sgn) (FL.selectionDepth (lambdaFrame sgn) 2)) FL.scale
      (DL : ℝ) (cL : ℝ)) :
    Measure.MeasureLBAt (lambdaTarget sgn) ((315113 / 10000 : ℚ) : ℝ) :=
  lambda_measure_of_const (lambdaFrame sgn) (by rw [lambdaFrame_d]; norm_num)
    (lambdaFrame_w_ne sgn) _ le_rfl (lambdaFrame_const sgn) hS hD

end CatalanCore.Uniform.Bank.Lambda
