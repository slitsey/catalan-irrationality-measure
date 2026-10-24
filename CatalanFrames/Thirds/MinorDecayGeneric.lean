module

public import CatalanCore.Decay.Rect.HybridHook
public import CatalanFrames.Thirds.Frame

@[expose] public section

/-! # Common-minor decay from any hybrid certificate (generic)

`HybCertData` bundles the hypotheses `hasDecay_commonMinorFam` takes about the certificate
`F : CertCoreGs sl ..`.  The certificate has no frame parameter: its validity does not involve the
frame's `xs`, `δ0` or `n0off`; those enter only through `Fr.DecayOKs' sl`.
-/

open CatalanCore CatalanCore.Rect
open CatalanLambda.Decay (Usig)
open CatalanCore.Decay (Unu Jfun)

namespace CatalanFrames.Thirds

/-- Hypotheses on a certificate for decay of the hybrid family at ratio `α`. -/
abbrev HybCertData {sl : ℝ} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : Cert.CertCoreGs sl K ρ ε c wt) (α : ℚ) (Rc : ℝ) (Inu D : ℚ) (dim : ℕ) :=
  HybridDecayData F α Rc Inu D dim

namespace HybCertData
export CatalanCore.HybridDecayData (mk hα hg hw0 hRc hc hInu hD hcc)
end HybCertData

/-- **Generic common-minor decay**: any frame with `DecayOKs' sl` and `Fr.d = dim`. -/
theorem thirds_minorDecay {sl : ℝ} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    {F : Cert.CertCoreGs sl K ρ ε c wt} {α : ℚ} {Rc : ℝ} {Inu D : ℚ} {dim : ℕ}
    (hF : HybCertData F α Rc Inu D dim) {Fr : Frame} (hFr : Fr.DecayOKs' sl) (hd : Fr.d = dim)
    {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (commonMinorFam Fr A dBudget) (D : ℝ) (F.ccert : ℝ) :=
  hF.commonMinorDecay hFr hd ha dBudget hA

end CatalanFrames.Thirds
