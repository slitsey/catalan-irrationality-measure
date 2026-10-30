import CatalanCore.Uniform.Bank.Sevenths.Final
import CatalanCore.Uniform.Bank.Sevenths.Frame
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform

/-- All six targets, conditional on the matched content and decay suppliers. -/
theorem sevenths_measure (a : Fin 6)
    (hS : HasScaledContent
      ((F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)).restrictAdm
        (fun i => i.1 % 2 = 0)) F7.scale Lam7)
    (hD : HasScaledDecay
      (F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2))
      F7.scale (D7 : ℝ) (c7 : ℝ)) :
    Measure.MeasureLBAt (seventhsTarget (seventhNumerator a)) ((70993 / 20 : ℚ) : ℝ) :=
  sevenths_measure_of_const (seventhsFrameAt a) (by show 1 ≤ 2; norm_num)
    (seventhsFrameAt_w_ne a) _ le_rfl (seventhsFrameAt_const a) hS hD

end CatalanCore.Uniform.Bank.Sevenths
