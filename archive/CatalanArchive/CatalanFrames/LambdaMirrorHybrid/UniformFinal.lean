module
public import CatalanFrames.HybCommon.DeficitProfile.Content
public import CatalanArchive.CatalanFrames.LambdaMirrorHybrid.MirFinalAll
@[expose] public section
open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
namespace CatalanFrames.LambdaMirrorHybrid

theorem mir_both_eps_uniform :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, HybCommon.DefBothG mirNInst r T δ ∧
      Real.log (DhybT mirNInst r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 :=
  HybCommon.profile_both_eps mirNInst mirNData (Or.inr rfl) mirN_tropFacts mirBad

/-- The same generic profile gives `μ(G+5π²/48)≤34.74`. -/
theorem mir_hyb_measure_uniform :
    Measure.MeasureLBAt ((∑'j : ℕ, (-1 : ℝ)^j/((2*j+1 : ℕ) : ℝ)^2)+5*Real.pi^2/48)
      ((1737/50 : ℚ) : ℝ) :=
  mir_hyb_measure_G (Λ := 184137/50000) (D := 39028/10000) (C := 76444/10000) (E := 1737/50)
    (mir_hasContent_of_both (by norm_num) (by
      simpa only [Rat.cast_div,Rat.cast_ofNat] using mir_both_eps_uniform))
    mir_hybrid_decay mir_mem2_decay (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms mir_hyb_measure_uniform
end CatalanFrames.LambdaMirrorHybrid
