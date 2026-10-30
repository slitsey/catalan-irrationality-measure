module

public import CatalanFrames.P6.Contour
public import CatalanCore.Decay.Integ

@[expose] public section

namespace CatalanFrames.P6.ContourPreparation

open CatalanCore
open CatalanFrames.P6

/-- The actual P6 frame admits every slope at least one. Private unbuilt template. -/
theorem p6_decayOK_atSlope {sl : ℝ} (hs : 1 ≤ sl) : p6Frame.DecayOKs' sl where
  contour := p6_contourOK
  slope := ⟨lt_of_lt_of_le zero_lt_one hs, hs, by convert hs using 1 <;> norm_num [p6Frame] <;> ring⟩
  atomRange := by
    intro i
    fin_cases i <;> simp [p6Frame] <;> norm_num
  norm_ge := by norm_num [p6Frame]

end CatalanFrames.P6.ContourPreparation

#print axioms CatalanFrames.P6.ContourPreparation.p6_decayOK_atSlope
