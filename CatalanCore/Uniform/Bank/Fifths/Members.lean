import CatalanCore.Uniform.Bank.Fifths.Final
import CatalanCore.Uniform.Bank.Fifths.Frame
set_option Elab.async false

/-! The four fifths members (lane B, B5): conditional `fifths_measure a` for `a = 1, 2, 3, 4`
(frames `fifths1 ... fifths4`, target `fifthsTarget a`).  The content and decay providers of the
new family `altGeom (2/9)` at the selection depth are explicit hypotheses. -/

namespace CatalanCore.Uniform.Bank.Fifths
open CatalanCore CatalanCore.Uniform

/-- **`fifths_measure 1`**: `mu(fifthsTarget 1) <= 59983/2500`, given the new-family content and
decay providers for `fifths1`. -/
theorem fifths1_measure
    (hS : HasScaledContent ((F5.family fifths1 (F5.selectionDepth fifths1 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family fifths1 (F5.selectionDepth fifths1 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 1) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_of_const fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _ le_rfl
    fifths1_const hS hD

/-- **`fifths_measure 2`**: `mu(fifthsTarget 2) <= 59983/2500`, given the new-family content and
decay providers for `fifths2`. -/
theorem fifths2_measure
    (hS : HasScaledContent ((F5.family fifths2 (F5.selectionDepth fifths2 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family fifths2 (F5.selectionDepth fifths2 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 2) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_of_const fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _ le_rfl
    fifths2_const hS hD

/-- **`fifths_measure 3`**: `mu(fifthsTarget 3) <= 59983/2500`, given the new-family content and
decay providers for `fifths3`. -/
theorem fifths3_measure
    (hS : HasScaledContent ((F5.family fifths3 (F5.selectionDepth fifths3 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family fifths3 (F5.selectionDepth fifths3 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 3) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_of_const fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _ le_rfl
    fifths3_const hS hD

/-- **`fifths_measure 4`**: `mu(fifthsTarget 4) <= 59983/2500`, given the new-family content and
decay providers for `fifths4`. -/
theorem fifths4_measure
    (hS : HasScaledContent ((F5.family fifths4 (F5.selectionDepth fifths4 2)).restrictAdm
      (fun i => i.1 % 2 = 0)) F5.scale Lam5)
    (hD : HasScaledDecay (F5.family fifths4 (F5.selectionDepth fifths4 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 4) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_measure_of_const fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _ le_rfl
    fifths4_const hS hD

end CatalanCore.Uniform.Bank.Fifths
