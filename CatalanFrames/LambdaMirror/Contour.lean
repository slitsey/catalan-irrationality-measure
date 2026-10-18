module

public import CatalanFrames.LambdaMirror.Frame
public import CatalanCore.Decay.RayBound

/-!
# Contour hypotheses for the mirror frame (WP8)

`mirFrame` (`xs = 5/8`, `δ0 = 3/8`, `n0off = 1`) satisfies `ContourOK`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem mirror_contourOK : mirFrame.ContourOK where
  xs_pos := by norm_num [mirFrame]
  gap := by
    refine ⟨by norm_num [mirFrame], fun i n => ?_⟩
    fin_cases i
    · exact Decay.gap_aux (1 / 4) (5 / 8) (3 / 8) 1 (by norm_num) (by norm_num) n
    · exact Decay.gap_aux 1 (5 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n

example := Frame.E_bound mirror_contourOK Decay.phiC_gt Decay.phiC_lt
  (Decay.cot_phiC' (by norm_num [mirFrame]))
example (N0 a b : ℕ) := Frame.contour_identity mirror_contourOK Decay.phiC_gt Decay.phiC_lt N0 a b

end CatalanFrames.LambdaMirror
