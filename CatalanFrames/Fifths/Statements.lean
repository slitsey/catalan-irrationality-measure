module
public import CatalanFrames.Fifths.MinorContent
public import CatalanFrames.Fifths.MinorDecayS
public import CatalanFrames.Fifths.MeasureAt
public import CatalanFrames.Fifths.IrrationalAt
@[expose] public section
open CatalanCore CatalanCore.Rect
namespace CatalanFrames.Fifths
/-! Closed target statements. This staged source is not a proved endpoint until its own build passes. -/
theorem fifths1_measure_3195 : Measure.MeasureLBAt (fifthsTarget 1) ((639/20 : ℚ) : ℝ) :=
  fifths1_measure_of_hyps fifths1_hasContent fifths1_minorDecayS
theorem fifths1_irrational : Irrational (fifthsTarget 1) :=
  fifths1_irrational_of_hyps fifths1_hasContent fifths1_minorDecayS
theorem fifths2_measure_3195 : Measure.MeasureLBAt (fifthsTarget 2) ((639/20 : ℚ) : ℝ) :=
  fifths2_measure_of_hyps fifths2_hasContent fifths2_minorDecayS
theorem fifths2_irrational : Irrational (fifthsTarget 2) :=
  fifths2_irrational_of_hyps fifths2_hasContent fifths2_minorDecayS
theorem fifths3_measure_3195 : Measure.MeasureLBAt (fifthsTarget 3) ((639/20 : ℚ) : ℝ) :=
  fifths3_measure_of_hyps fifths3_hasContent fifths3_minorDecayS
theorem fifths3_irrational : Irrational (fifthsTarget 3) :=
  fifths3_irrational_of_hyps fifths3_hasContent fifths3_minorDecayS
theorem fifths4_measure_3195 : Measure.MeasureLBAt (fifthsTarget 4) ((639/20 : ℚ) : ℝ) :=
  fifths4_measure_of_hyps fifths4_hasContent fifths4_minorDecayS
theorem fifths4_irrational : Irrational (fifthsTarget 4) :=
  fifths4_irrational_of_hyps fifths4_hasContent fifths4_minorDecayS
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_measure_3195
#print axioms CatalanFrames.Fifths.fifths1_irrational
#print axioms CatalanFrames.Fifths.fifths2_measure_3195
#print axioms CatalanFrames.Fifths.fifths2_irrational
#print axioms CatalanFrames.Fifths.fifths3_measure_3195
#print axioms CatalanFrames.Fifths.fifths3_irrational
#print axioms CatalanFrames.Fifths.fifths4_measure_3195
#print axioms CatalanFrames.Fifths.fifths4_irrational
