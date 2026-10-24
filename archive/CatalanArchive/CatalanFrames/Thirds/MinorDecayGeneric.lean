module

public import CatalanCore.Decay.Rect.DecayMinor
public import CatalanFrames.Thirds.Frame

@[expose] public section
open CatalanFrames.Thirds

/-! # Common-minor decay from any hybrid certificate (generic)

`HybCertData` bundles the hypotheses `hasDecay_commonMinorFam` takes about the certificate
`F : CertCoreGs sl ..`.  The certificate has no frame parameter: its validity does not involve the
frame's `xs`, `δ0` or `n0off`; those enter only through `Fr.DecayOKs' sl`.
-/

open CatalanCore CatalanCore.Rect
open CatalanLambda.Decay (Usig)
open CatalanCore.Decay (Unu Jfun)

namespace CatalanArchive.CatalanFrames.Thirds.MinorDecayGeneric

/-- Hypotheses on a certificate for decay of the hybrid family at ratio `α`. -/
structure HybCertData {sl : ℝ} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : Cert.CertCoreGs sl K ρ ε c wt) (α : ℚ) (Rc : ℝ) (Inu : ℚ) (D : ℚ) (dim : ℕ) : Prop where
  hα : 0 < α
  hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
        + (1 - ε) * Real.pi * |s.im|
  hw0 : ∀ k, 0 ≤ wt k
  hRc : 0 ≤ Rc
  hc : ∀ k, ‖c k‖ ≤ Rc
  hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)
  hD : D ≤ F.Dof dim α Inu
  hcc : 0 ≤ (F.ccert : ℝ)

/-- **Generic common-minor decay**: any frame with `DecayOKs' sl` and `Fr.d = dim`. -/
theorem thirds_minorDecay {sl : ℝ} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    {F : Cert.CertCoreGs sl K ρ ε c wt} {α : ℚ} {Rc : ℝ} {Inu D : ℚ} {dim : ℕ}
    (hF : HybCertData F α Rc Inu D dim) {Fr : Frame} (hFr : Fr.DecayOKs' sl) (hd : Fr.d = dim)
    {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (commonMinorFam Fr A dBudget) (D : ℝ) (F.ccert : ℝ) :=
  hasDecay_commonMinorFam hFr F hF.hα ha hF.hg hF.hw0 hF.hRc hF.hc hF.hInu
    (by rw [hd]; exact hF.hD) hF.hcc dBudget hA

end CatalanArchive.CatalanFrames.Thirds.MinorDecayGeneric
