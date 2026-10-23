module

public import CatalanFrames.Lambda.HybContent
public import CatalanFrames.LambdaHybrid.Assembly

@[expose] public section

/-! Scaling transfer from the pair family of `lamFrame` to `G - 5π²/48` (no decay certificate). -/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

/-- Transfer a measure bound for the pair family `lamFrame.const` to the form `G - 5π²/48`
(generic scaling lemma). -/
theorem lam_pairMeasure_G {E : ℚ} (hE0 : 0 ≤ E) (h : (hybPairFam lamFrame 8).MeasureLB (E : ℝ)) :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (E : ℝ) := by
  have h' : Measure.MeasureLBAt lamFrame.const (E : ℝ) := h
  rw [const_eq] at h'
  have := h'.affine (by exact_mod_cast hE0) 2 0 (by norm_num)
  convert this using 1
  push_cast
  ring

end CatalanFrames.LambdaHybrid
