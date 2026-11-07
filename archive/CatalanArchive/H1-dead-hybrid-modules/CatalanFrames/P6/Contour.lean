module

public import CatalanFrames.P6.Frame
public import CatalanCore.Decay.RayBound

/-!
# Contour hypotheses for the P6 frame (CLEAN1)

`p6Frame` (`xs = 3/4`, `δ0 = 1/4`) satisfies `ContourOK`.  The frame is defined once, in
`CatalanFrames.P6.Frame`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.P6

theorem p6_contourOK : p6Frame.ContourOK where
  xs_pos := by norm_num [p6Frame]
  gap := by
    refine ⟨by norm_num [p6Frame], fun i n => ?_⟩
    fin_cases i
    · exact Decay.gap_aux 1 (3 / 4) (1 / 4) 0 (by norm_num) (by norm_num) n
    · exact Decay.gap_aux (1 / 3) (3 / 4) (1 / 4) 1 (by norm_num) (by norm_num) n
    · exact Decay.gap_aux (1 / 2) (3 / 4) (1 / 4) 1 (by norm_num) (by norm_num) n

example := Frame.E_bound p6_contourOK Decay.phiC_gt Decay.phiC_lt
  (Decay.cot_phiC' (by norm_num [p6Frame]))
example (N0 a b : ℕ) := Frame.contour_identity p6_contourOK Decay.phiC_gt Decay.phiC_lt N0 a b

end CatalanFrames.P6
