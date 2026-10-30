import CatalanCore.Uniform.Bank.FifthsContent.Content5
import CatalanCore.Uniform.Bank.FifthsContent.NoUF
import CatalanCore.Uniform.Bank.Fifths.Frame
set_option Elab.async false

/-! # The four fifths members without UF (lane B, B5c)

`fifthsK_noUF_measure`: `μ(fifthsTarget K) ≤ 243052/10000` from the new-family decay provider alone;
the content hypothesis is discharged by `fifths_content_noUF`. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths

theorem cFr_fifths1 : cFr fifths1 ≤ 49 := by
  unfold cFr Dc Dm
  simp [Fin.sum_univ_two, fifths1, fifthsFrame]
  norm_num

theorem cFr_fifths2 : cFr fifths2 ≤ 49 := by
  unfold cFr Dc Dm
  simp [Fin.sum_univ_two, fifths2, fifthsFrame]
  norm_num

theorem cFr_fifths3 : cFr fifths3 ≤ 49 := by
  unfold cFr Dc Dm
  simp [Fin.sum_univ_two, fifths3, fifthsFrame]
  norm_num

theorem cFr_fifths4 : cFr fifths4 ≤ 49 := by
  unfold cFr Dc Dm
  simp [Fin.sum_univ_two, fifths4, fifthsFrame]
  norm_num

theorem depth_fifths (Fr : Frame) (hd : Fr.d = 2) : F5.selectionDepth Fr 2 ≤ 1000 := by
  unfold BlockGeom.selectionDepth BlockGeom.allComponents BlockGeom.commonComponents
  rw [hd]
  decide +kernel

theorem fifths1_noUF_measure
    (hD : HasScaledDecay (F5.family fifths1 (F5.selectionDepth fifths1 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 1) ((243052 / 10000 : ℚ) : ℝ) :=
  fifths_noUF_measure_of_const fifths1 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths1_const
    (fifths_content_noUF fifths1_shift _ cFr_fifths1 (depth_fifths fifths1 rfl)) hD

theorem fifths2_noUF_measure
    (hD : HasScaledDecay (F5.family fifths2 (F5.selectionDepth fifths2 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 2) ((243052 / 10000 : ℚ) : ℝ) :=
  fifths_noUF_measure_of_const fifths2 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths2_const
    (fifths_content_noUF fifths2_shift _ cFr_fifths2 (depth_fifths fifths2 rfl)) hD

theorem fifths3_noUF_measure
    (hD : HasScaledDecay (F5.family fifths3 (F5.selectionDepth fifths3 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 3) ((243052 / 10000 : ℚ) : ℝ) :=
  fifths_noUF_measure_of_const fifths3 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths3_const
    (fifths_content_noUF fifths3_shift _ cFr_fifths3 (depth_fifths fifths3 rfl)) hD

theorem fifths4_noUF_measure
    (hD : HasScaledDecay (F5.family fifths4 (F5.selectionDepth fifths4 2)) F5.scale
      (D5 : ℝ) (c5 : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 4) ((243052 / 10000 : ℚ) : ℝ) :=
  fifths_noUF_measure_of_const fifths4 (by show 1 ≤ 2; norm_num) (fifthsFrame_w_ne _ _ _ _ _ _) _
    le_rfl fifths4_const
    (fifths_content_noUF fifths4_shift _ cFr_fifths4 (depth_fifths fifths4 rfl)) hD

#print axioms fifths1_noUF_measure
end CatalanCore.Uniform.Bank.FifthsContent
