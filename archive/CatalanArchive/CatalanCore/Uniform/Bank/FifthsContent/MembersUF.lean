import CatalanCore.Uniform.Bank.FifthsContent.ContentUF
import CatalanCore.Uniform.Bank.FifthsContent.Members
import CatalanCore.Uniform.Bank.FifthsContent.UFNum
import CatalanCore.Uniform.Bank.Fifths.Frame
set_option Elab.async false

/-! # The four fifths members with UF (lane B, B5c)

`fifthsK_UF_measure`: `μ(fifthsTarget K) ≤ 243052/10000` from the new-family decay provider alone;
the content hypothesis is discharged by `fifths_content_UF`. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths

theorem fifths1_UF_measure
    (hD : HasScaledDecay (F5.family fifths1 (F5.selectionDepth fifths1 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 1) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_UF_measure_of_const fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths1_const
    (fifths_content_UF fifths1_shift _ cFr_fifths1 (depth_fifths fifths1 rfl)) hD

theorem fifths2_UF_measure
    (hD : HasScaledDecay (F5.family fifths2 (F5.selectionDepth fifths2 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 2) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_UF_measure_of_const fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths2_const
    (fifths_content_UF fifths2_shift _ cFr_fifths2 (depth_fifths fifths2 rfl)) hD

theorem fifths3_UF_measure
    (hD : HasScaledDecay (F5.family fifths3 (F5.selectionDepth fifths3 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 3) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_UF_measure_of_const fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths3_const
    (fifths_content_UF fifths3_shift _ cFr_fifths3 (depth_fifths fifths3 rfl)) hD

theorem fifths4_UF_measure
    (hD : HasScaledDecay (F5.family fifths4 (F5.selectionDepth fifths4 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 4) ((59983 / 2500 : ℚ) : ℝ) :=
  fifths_UF_measure_of_const fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths4_const
    (fifths_content_UF fifths4_shift _ cFr_fifths4 (depth_fifths fifths4 rfl)) hD

#print axioms fifths1_UF_measure
end CatalanCore.Uniform.Bank.FifthsContent
