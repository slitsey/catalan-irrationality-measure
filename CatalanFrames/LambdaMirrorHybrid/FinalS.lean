module

public import CatalanFrames.HybCommon.DeficitProfile.MergedRows
public import CatalanFrames.LambdaMirrorHybrid.MergedContent
public import CatalanFrames.LambdaMirrorHybrid.DecayS

@[expose] public section

/-!
# λ′ final: `μ(G + 5π²/48) ≤ 32.44` (slope-`5/2` decay, merged non-clean content)
-/

open Filter

namespace CatalanFrames.LambdaMirrorHybrid

theorem mir_hyb_measure_final2 :
    CatalanCore.Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      + 5 * Real.pi ^ 2 / 48) (((811 / 25 : ℚ)) : ℝ) :=
  mir_hyb_measure_final2_of mir_both_eps_merged (by norm_num [HybCommon.mergedLambda])
    (by norm_num [HybCommon.mergedLambda])

#print axioms mir_hyb_measure_final2

end CatalanFrames.LambdaMirrorHybrid
