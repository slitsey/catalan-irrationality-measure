module
public import CatalanFrames.HybCommon.DeficitProfile.Content
public import CatalanFrames.LambdaHybrid.AssemblyFinal
@[expose] public section
open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda
namespace CatalanFrames.LambdaHybrid

theorem lam_both_eps_uniform :
    ∀ε>0, ∀ᶠr : ℕ in atTop, ∃T δ : ℕ→ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r/8) T δ)≤((184137/50000 : ℝ)+ε)*(r : ℝ)^2 :=
  HybCommon.profile_both_eps lamInst lamData (Or.inl rfl) lam_tropFacts lam_badInfo

/-- The uniform rescaled-core profile gives `μ(G-5π²/48)≤34.74`. -/
theorem lam_hyb_measure_uniform :
    Measure.MeasureLBAt ((∑'j : ℕ, (-1 : ℝ)^j/((2*j+1 : ℕ) : ℝ)^2)-5*Real.pi^2/48)
      ((1737/50 : ℚ) : ℝ) :=
  lam_hyb_measure_of_both (Λ := 184137/50000) (E := 1737/50)
    (by simpa only [Rat.cast_div,Rat.cast_ofNat] using lam_both_eps_uniform)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms lam_hyb_measure_uniform
end CatalanFrames.LambdaHybrid
