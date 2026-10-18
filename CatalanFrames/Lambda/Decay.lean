module

public import CatalanFrames.Lambda.PolyEval
public import CatalanFrames.Lambda.Const
public import CatalanLambda.Decay.ThmNAsymp

/-!
# λ decay: `HasDecay (ofFrame lamFrame) D_cert c_cert` from the legacy window corollary

Generic in the legacy certificate facts `F`.  The `ContourGap` hypothesis is not needed here:
the legacy window result is used as is.
-/

@[expose] public section

open CatalanCore

namespace CatalanFrames.Lambda

theorem hasDecay {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CatalanLambda.Decay.CertFacts K ρ ε c m) :
    HasDecay (PolyFamily.ofFrame lamFrame) (F.Dcert : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨N, H⟩ := CatalanLambda.Decay.window_liminf_P F hδ
  refine ⟨N, fun (n : ℕ) _ hn t ht => ?_⟩
  have := H n hn t ht
  show |(Polynomial.aeval (lamFrame.const + t) (lamFrame.Ppoly n))| ≤ _
  rw [Frame.aeval_Ppoly_real, M_eq, const_eq_lamS]
  exact this

end CatalanFrames.Lambda
