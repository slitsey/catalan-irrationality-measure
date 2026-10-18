module

public import CatalanFrames.Lambda.Frame
public import CatalanCore.Decay.RayBound

/-!
# Contour hypotheses for the λ frame (CLEAN1)

`lamFrame` (`xs = 3/8`, `δ0 = 3/8`) satisfies `ContourOK`; the generic `E_bound` and contour
identity instantiate at it.  The frame itself is defined once, in `CatalanFrames.Lambda.Frame`.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

theorem lam_contourOK : lamFrame.ContourOK where
  xs_pos := by norm_num [lamFrame]
  gap := by
    refine ⟨by norm_num [lamFrame], fun i n => ?_⟩
    fin_cases i
    · exact Decay.gap_aux (3 / 4) (3 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n
    · exact Decay.gap_aux 1 (3 / 8) (3 / 8) 0 (by norm_num) (by norm_num) n

example := Frame.E_bound lam_contourOK Decay.phiC_gt Decay.phiC_lt
  (Decay.cot_phiC' (by norm_num [lamFrame]))
example (N0 a b : ℕ) := Frame.contour_identity lam_contourOK Decay.phiC_gt Decay.phiC_lt N0 a b

end CatalanFrames.Lambda
