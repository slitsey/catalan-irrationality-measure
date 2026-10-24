module

public import CatalanFrames.Thirds.MinorDecayGeneric
public import CatalanFrames.Thirds.ContourInstances
public import CatalanCore.Cert.SigmaHybS.FrameDecay

@[expose] public section

/-! # M8: common-minor decay for the thirds frames from the shift certificate `certS`

The only module of the thirds package importing the `certS` closure.  `certS` is a
`CertCoreGs (5/2) ..` with no frame argument, so it is valid for every frame with
`DecayOKs' (5/2)` and `d = 2`; `xs`, `n0off` of the frame are irrelevant to it.
`D = 3.90557`, `c = 18386549/2500000 = 7.3546196`, `α = 1/8`.
-/

open CatalanCore CatalanCore.Rect CatalanCore.Cert.SigmaHybS

namespace CatalanFrames.Thirds

theorem certS_hybCertData :
    HybCertData certS (1 / 8) 2 (17024457 / 10 ^ 7) (390557 / 100000) 2 :=
  Data.certified

/-- **M8.** Any `DecayOKs' (5/2)` frame with `d = 2`: decay of the common-minor family. -/
theorem hasDecay_commonMinorFam_certS {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ))
    (hd : Fr.d = 2) {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam Fr A dBudget) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) := by
  have h := thirds_minorDecay certS_hybCertData hFr hd ha dBudget hA
  have e : certS.ccert = 18386549 / 2500000 := rfl
  rw [e] at h
  exact h

theorem thirdsAc_minorDecay {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam thirdsAc A dBudget) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  hasDecay_commonMinorFam_certS thirdsAc_decayOKs'_52 rfl ha dBudget hA

theorem thirdsBc_minorDecay {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam thirdsBc A dBudget) (((390557 / 100000 : ℚ)) : ℝ)
      (((18386549 / 2500000 : ℚ)) : ℝ) :=
  hasDecay_commonMinorFam_certS thirdsBc_decayOKs'_52 rfl ha dBudget hA

#print axioms hasDecay_commonMinorFam_certS
#print axioms thirdsAc_minorDecay
#print axioms thirdsBc_minorDecay

end CatalanFrames.Thirds
