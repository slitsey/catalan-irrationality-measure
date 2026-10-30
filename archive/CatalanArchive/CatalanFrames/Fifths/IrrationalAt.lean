module
public import CatalanFrames.HybGen.IrrationalAssembly
public import CatalanFrames.Fifths.Nonvanishing
public import CatalanFrames.Fifths.Tables
public import CatalanFrames.Fifths.TargetConstants
public import CatalanCore.Measure.Scaling
@[expose] public section
open CatalanCore CatalanCore.Rect
namespace CatalanFrames.Fifths
/-! Conditional irrationality endpoints; Content and Decay remain explicit hypotheses. -/
theorem fifths1_irrational_of_hyps
    (hC : HasContent (commonMinorFam fifths1 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths1 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Irrational (fifthsTarget 1) := by
  have hI := HybGen.irrational_of_pin_one (commonMinorFam fifths1 FifthsAdm 1)
    30 (by norm_num) unitClasses (by decide)
    hC hD (by norm_num [fifthsPrice]) fifths1_NV
  have hT : (fifthsTarget 1 : ℝ) = ((-25 : ℚ) : ℝ)*fifths1.const+((0 : ℚ) : ℝ) := by
    rw [fifths1_const]
    norm_num <;> ring
  rw [hT]
  exact Measure.irrational_affine hI (-25) 0 (by norm_num)
theorem fifths2_irrational_of_hyps
    (hC : HasContent (commonMinorFam fifths2 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths2 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Irrational (fifthsTarget 2) := by
  have hI := HybGen.irrational_of_pin_one (commonMinorFam fifths2 FifthsAdm 1)
    30 (by norm_num) unitClasses (by decide)
    hC hD (by norm_num [fifthsPrice]) fifths2_NV
  have hT : (fifthsTarget 2 : ℝ) = ((-25 : ℚ) : ℝ)*fifths2.const+((0 : ℚ) : ℝ) := by
    rw [fifths2_const]
    norm_num <;> ring
  rw [hT]
  exact Measure.irrational_affine hI (-25) 0 (by norm_num)
theorem fifths3_irrational_of_hyps
    (hC : HasContent (commonMinorFam fifths3 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths3 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Irrational (fifthsTarget 3) := by
  have hI := HybGen.irrational_of_pin_one (commonMinorFam fifths3 FifthsAdm 1)
    30 (by norm_num) unitClasses (by decide)
    hC hD (by norm_num [fifthsPrice]) fifths3_NV
  have hT : (fifthsTarget 3 : ℝ) = ((-25 : ℚ) : ℝ)*fifths3.const+((0 : ℚ) : ℝ) := by
    rw [fifths3_const]
    norm_num <;> ring
  rw [hT]
  exact Measure.irrational_affine hI (-25) 0 (by norm_num)
theorem fifths4_irrational_of_hyps
    (hC : HasContent (commonMinorFam fifths4 FifthsAdm 1) (fifthsPrice : ℝ))
    (hD : HasDecay (commonMinorFam fifths4 FifthsAdm 1)
      ((390557/100000 : ℚ) : ℝ) ((18386549/2500000 : ℚ) : ℝ)) :
    Irrational (fifthsTarget 4) := by
  have hI := HybGen.irrational_of_pin_one (commonMinorFam fifths4 FifthsAdm 1)
    30 (by norm_num) unitClasses (by decide)
    hC hD (by norm_num [fifthsPrice]) fifths4_NV
  have hT : (fifthsTarget 4 : ℝ) = ((-25 : ℚ) : ℝ)*fifths4.const+((0 : ℚ) : ℝ) := by
    rw [fifths4_const]
    norm_num <;> ring
  rw [hT]
  exact Measure.irrational_affine hI (-25) 0 (by norm_num)
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_irrational_of_hyps
#print axioms CatalanFrames.Fifths.fifths2_irrational_of_hyps
#print axioms CatalanFrames.Fifths.fifths3_irrational_of_hyps
#print axioms CatalanFrames.Fifths.fifths4_irrational_of_hyps
