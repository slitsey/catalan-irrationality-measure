module
public import CatalanFrames.HybGen.MeasureAssembly
public import CatalanFrames.Fifths.Nonvanishing
public import CatalanFrames.Fifths.Tables
public import CatalanFrames.Fifths.TargetConstants
public import CatalanFrames.Thirds.Assembly
@[expose] public section
open CatalanCore CatalanCore.Rect
namespace CatalanFrames.Fifths
/-! Conditional target endpoints: actual ContentData/Covers/content are still separate gates. -/
theorem fifths1_measure_of_hyps
    (hC : HasContent (commonMinorFam fifths1 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths1 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 1) ((639/20 : ℚ) : ℝ) := by
  have hM := HybGen.measure_of_class_window (commonMinorFam fifths1 FifthsAdm 1) 30 unitClasses
    (Λ := fifthsPrice) (D := 390557/100000) (c := 18386549/2500000) (E := 639/20)
    hC hD (by norm_num [fifthsPrice]) (by norm_num) (by norm_num [fifthsPrice])
    fifths1_NV window_fifths fifths_exponent_check
  exact Thirds.measureLBAt_of_const (a := -1/25) (by norm_num) (by norm_num) fifths1_const hM
theorem fifths2_measure_of_hyps
    (hC : HasContent (commonMinorFam fifths2 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths2 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 2) ((639/20 : ℚ) : ℝ) := by
  have hM := HybGen.measure_of_class_window (commonMinorFam fifths2 FifthsAdm 1) 30 unitClasses
    (Λ := fifthsPrice) (D := 390557/100000) (c := 18386549/2500000) (E := 639/20)
    hC hD (by norm_num [fifthsPrice]) (by norm_num) (by norm_num [fifthsPrice])
    fifths2_NV window_fifths fifths_exponent_check
  exact Thirds.measureLBAt_of_const (a := -1/25) (by norm_num) (by norm_num) fifths2_const hM
theorem fifths3_measure_of_hyps
    (hC : HasContent (commonMinorFam fifths3 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths3 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 3) ((639/20 : ℚ) : ℝ) := by
  have hM := HybGen.measure_of_class_window (commonMinorFam fifths3 FifthsAdm 1) 30 unitClasses
    (Λ := fifthsPrice) (D := 390557/100000) (c := 18386549/2500000) (E := 639/20)
    hC hD (by norm_num [fifthsPrice]) (by norm_num) (by norm_num [fifthsPrice])
    fifths3_NV window_fifths fifths_exponent_check
  exact Thirds.measureLBAt_of_const (a := -1/25) (by norm_num) (by norm_num) fifths3_const hM
theorem fifths4_measure_of_hyps
    (hC : HasContent (commonMinorFam fifths4 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths4 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Measure.MeasureLBAt (fifthsTarget 4) ((639/20 : ℚ) : ℝ) := by
  have hM := HybGen.measure_of_class_window (commonMinorFam fifths4 FifthsAdm 1) 30 unitClasses
    (Λ := fifthsPrice) (D := 390557/100000) (c := 18386549/2500000) (E := 639/20)
    hC hD (by norm_num [fifthsPrice]) (by norm_num) (by norm_num [fifthsPrice])
    fifths4_NV window_fifths fifths_exponent_check
  exact Thirds.measureLBAt_of_const (a := -1/25) (by norm_num) (by norm_num) fifths4_const hM
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_measure_of_hyps
#print axioms CatalanFrames.Fifths.fifths2_measure_of_hyps
#print axioms CatalanFrames.Fifths.fifths3_measure_of_hyps
#print axioms CatalanFrames.Fifths.fifths4_measure_of_hyps
