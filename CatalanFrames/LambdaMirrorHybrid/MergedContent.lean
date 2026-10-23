module
public import CatalanFrames.HybCommon.DeficitProfile.MergedRows
public import CatalanFrames.LambdaMirrorHybrid.MirFinalAll
@[expose] public section
open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
namespace CatalanFrames.LambdaMirrorHybrid

/-- Merged (non-clean two-level) content bound for the mirror pair (`G + 5π²/48`). -/
theorem mir_both_eps_merged :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, HybCommon.DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r/8) T δ)≤(((HybCommon.mergedLambda : ℚ) : ℝ)+ε)*(r : ℝ)^2 :=
  HybCommon.merged_both_eps mirNInst mirNData (Or.inr rfl) mirN_tropFacts mirBad

#print axioms mir_both_eps_merged
end CatalanFrames.LambdaMirrorHybrid
