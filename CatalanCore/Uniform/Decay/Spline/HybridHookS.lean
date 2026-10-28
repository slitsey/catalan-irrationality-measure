module

public import CatalanCore.Decay.Rect.HybridHook
public import CatalanCore.Uniform.Decay.Spline.ChainWin

@[expose] public section

/-!
# Signed hybrid decay hooks (lane D, package D2)

`HybridDecayDataS` is `HybridDecayData` with the nonnegativity `hw0` replaced by a presentation
variation bound `hwV : ∑ |wt k| ≤ V`; same conclusions (`hybridDecay`, `membersDecay`, `pairDecay`,
`commonMinorDecay`), via the signed chain.
-/

open CatalanCore.Rect
open CatalanLambda.Decay (Usig)
open CatalanCore.Decay (Unu Jfun)

namespace CatalanCore.SignedChain

/-- The frame-independent data needed by all hybrid decay routes. -/
structure HybridDecayDataS {sl : ℝ} {K : ℕ} {ρ ε : ℝ}
    {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : Cert.CertCoreGs sl K ρ ε c wt) (α : ℚ) (Rc V : ℝ)
    (Inu D : ℚ) (dim : ℕ) : Prop where
  hα : 0 < α
  hg : ∀ s : ℂ, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu (α : ℝ) s
    + (1 - ε) * Real.pi * |s.im|
  hwV : ∑ k, |wt k| ≤ V
  hRc : 0 ≤ Rc
  hc : ∀ k, ‖c k‖ ≤ Rc
  hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)
  hD : D ≤ F.Dof dim α Inu
  hcc : 0 ≤ (F.ccert : ℝ)

namespace HybridDecayDataS

variable {sl : ℝ} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
  {F : Cert.CertCoreGs sl K ρ ε c wt} {α : ℚ} {Rc V : ℝ} {Inu D : ℚ} {dim : ℕ}
  (hF : HybridDecayDataS F α Rc V Inu D dim) {Fr : Frame}
  (hFr : Fr.DecayOKs' sl) (hd : Fr.d = dim)

include hF hFr hd

/-- The full family at any positive certified border ratio. -/
theorem hybridDecay :
    HasDecay (hybridFamUp Fr α) (D : ℝ) (F.ccert : ℝ) :=
  decay_of_certG_rect_slope hFr F hF.hα hF.hg hF.hwV hF.hRc hF.hc
    hF.hInu (by rw [hd]; exact hF.hD)

/-- Both members on any admissibility relation inside the certified window. -/
theorem membersDecay {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    Mem1DecayA Fr A (D : ℝ) (F.ccert : ℝ) ∧
      Mem2DecayA Fr A (D : ℝ) (F.ccert : ℝ) :=
  ⟨mem1DecayA_of_certG_rect_slack_slope hFr F hF.hα hF.hg hF.hwV hF.hRc hF.hc
      hF.hInu (by rw [hd]; exact hF.hD) ha hA,
    mem2DecayA_of_certG_rect_slack_slope hFr F hF.hα hF.hg hF.hwV hF.hRc hF.hc
      hF.hInu (by rw [hd]; exact hF.hD) hF.hcc ha hA⟩

/-- The paired family uses exactly the same data and leading constants. -/
theorem pairDecay {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (hybPairFamA Fr A) (D : ℝ) (F.ccert : ℝ) := by
  obtain ⟨h1, h2⟩ := hF.membersDecay hFr hd ha hA
  exact hasDecay_hybPairA hF.hcc h1 h2

/-- Any fixed common-deletion budget uses the same certified constants. -/
theorem commonMinorDecay {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ)
    {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (α : ℝ) * r ≤ m ∧ (m : ℝ) ≤ α * r + a) :
    HasDecay (commonMinorFam Fr A dBudget) (D : ℝ) (F.ccert : ℝ) :=
  hasDecay_commonMinorFam hFr F hF.hα ha hF.hg hF.hwV hF.hRc hF.hc hF.hInu
    (by rw [hd]; exact hF.hD) hF.hcc dBudget hA



end HybridDecayDataS
end CatalanCore.SignedChain
