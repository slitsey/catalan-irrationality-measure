module

public import CatalanFrames.Thirds.MinorDecayGeneric
public import CatalanFrames.Thirds.ContourInstances
public import CatalanCore.Cert.SigmaThirds.Data

@[expose] public section

/-! # Common-minor decay from the thirds-specific certificate

The generic adapter supplies both signs from the same frame-independent certificate.
-/

open CatalanCore CatalanCore.Rect CatalanCore.Cert.SigmaThirds

namespace CatalanFrames.Thirds

theorem certS_hybCertDataT :
    HybCertData certS (1 / 8) 2 (17024457 / 10 ^ 7) (77423 / 20000) 2 :=
  Data.certified

/-- Any slope-`5/2` decay frame of dimension two inherits the common-minor bound. -/
theorem hasDecay_commonMinorFam_certT {Fr : Frame} (hFr : Fr.DecayOKs' (5 / 2 : ℝ))
    (hd : Fr.d = 2) {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧
      (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam Fr A dBudget) (((77423 / 20000 : ℚ)) : ℝ)
      (((169697 / 25000 : ℚ)) : ℝ) := by
  have h := thirds_minorDecay certS_hybCertDataT hFr hd ha dBudget hA
  have e : certS.ccert = 169697 / 25000 := rfl
  rw [e] at h
  exact h

theorem thirdsAc_minorDecayT {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ)
    {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧
      (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam thirdsAc A dBudget) (((77423 / 20000 : ℚ)) : ℝ)
      (((169697 / 25000 : ℚ)) : ℝ) :=
  hasDecay_commonMinorFam_certT thirdsAc_decayOKs'_52 rfl ha dBudget hA

theorem thirdsBc_minorDecayT {a : ℝ} (ha : 0 ≤ a) (dBudget : ℕ)
    {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧
      (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + a) :
    HasDecay (commonMinorFam thirdsBc A dBudget) (((77423 / 20000 : ℚ)) : ℝ)
      (((169697 / 25000 : ℚ)) : ℝ) :=
  hasDecay_commonMinorFam_certT thirdsBc_decayOKs'_52 rfl ha dBudget hA

#print axioms hasDecay_commonMinorFam_certT
#print axioms thirdsAc_minorDecayT
#print axioms thirdsBc_minorDecayT

end CatalanFrames.Thirds
