module
public import CatalanFrames.HybCommon.DeficitProfile.MergedRows
public import CatalanFrames.LambdaHybrid.AssemblyFinal
@[expose] public section
open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda
namespace CatalanFrames.LambdaHybrid

/-- Merged (non-clean two-level) content bound for the first member pair of `G - 5π²/48`:
`log DhybT ≤ (Λ_new + ε) r²` with `Λ_new = HybCommon.mergedLambda`. -/
theorem lam_both_eps_merged :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r/8) T δ)≤(((HybCommon.mergedLambda : ℚ) : ℝ)+ε)*(r : ℝ)^2 :=
  HybCommon.merged_both_eps lamInst lamData (Or.inl rfl) lam_tropFacts lam_badInfo

#print axioms lam_both_eps_merged
end CatalanFrames.LambdaHybrid
