module

public import CatalanFrames.HybCommon.DeficitProfile.MergedRows
public import CatalanFrames.LambdaHybrid.MergedContent
public import CatalanFrames.LambdaHybrid.DecayS

@[expose] public section

/-!
# λ final: `μ(G - 5π²/48) ≤ 32.44` (slope-`5/2` decay, merged non-clean content)

`c/(D - Λ_new) = 7.3546196/(3.90557 - 3.6788498…) = 32.4390…`.
-/

open Filter

namespace CatalanFrames.LambdaHybrid

theorem lam_hyb_measure_final2 :
    CatalanCore.Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      - 5 * Real.pi ^ 2 / 48) (((811 / 25 : ℚ)) : ℝ) :=
  lam_hyb_measure_final2_of lam_both_eps_merged (by norm_num [HybCommon.mergedLambda])
    (by norm_num [HybCommon.mergedLambda])

#print axioms lam_hyb_measure_final2

end CatalanFrames.LambdaHybrid
