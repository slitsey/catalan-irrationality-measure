module

public import CatalanFrames.LambdaMirror.Const
public import CatalanFrames.LambdaMirror.Frame
public import CatalanArchive.CatalanLambda.Mirror.Window

/-!
# Mirror decay: `HasDecay (ofFrame mirFrame) D_cert c_cert` from the legacy mirror window corollary
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.LambdaMirror

theorem hasDecay {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CatalanLambda.Decay.CertFacts K ρ ε c m) :
    HasDecay (PolyFamily.ofFrame mirFrame) (F.Dcert : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, H⟩ := CatalanLambda.Mirror.window_liminf_PB F hδ
  refine ⟨N, fun (n : ℕ) _ hn t ht => ?_⟩
  have := H n hn t ht
  show |(Polynomial.aeval (mirFrame.const + t) (mirFrame.Ppoly n))| ≤ _
  rw [Frame.aeval_Ppoly_real, M_eq, const_eq_lamB]
  exact this

end CatalanFrames.LambdaMirror
