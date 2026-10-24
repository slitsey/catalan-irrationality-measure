module

public import CatalanMeasure.GenD.Analytic.First

@[expose] public section

/-!
# Scaling lemmas for trial sequences (design-free)

`barrierTrialT (c u) = c * barrierTrialT u` and the same for the squared norm.  (Generic versions
of the lemmas of `Parametric.TwentyTrialFields`, so that no P20 module is needed.)
-/

namespace CatalanMeasure.GenD

open OAI.InternalCatalan

noncomputable section

theorem barrierTrialT_scale (c : ℝ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (fun j => c * u j) x = c * barrierTrialT u x := by
  unfold barrierTrialT
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

theorem barrierTrialNormSq_scale (c : ℝ) (u : ℕ → ℝ) :
    barrierTrialNormSq (fun j => c * u j) = c ^ 2 * barrierTrialNormSq u := by
  unfold barrierTrialNormSq
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

end

end CatalanMeasure.GenD
