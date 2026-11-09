module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Member
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section
set_option Elab.async false

/-! # Geometry transport of every retained dip member (R06, ID-G1)
No geometry slope, support, frame or affine price is fixed. The full feasible
pivot dual is supplied; numeric count-price checks remain in finite instances.
-/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Arith.Hybrid
open Finset

theorem alt_member_gle_of_dual
    (g : ℚ) (hg : 0 < g) (Fr : Frame) (depth r m p : ℕ) [Fact p.Prime]
    (hm : m = (altGeom g hg).borderSize r) (hr : r % 2 = 0)
    (S : Finset ((altGeom g hg).geometry r).C)
    (pR pC : Fin m → Option (Fin r)) (lR lC VR VC : Fin m → ℚ)
    (hP : HybPiv r m p Fr pR pC lR lC VR VC)
    (ρ γ : Fin r ⊕ Fin m → ℚ) (hρ : ∀ x, 0 ≤ ρ x) (hγ : ∀ y, 0 ≤ γ y)
    (hf : ∀ x y, ((Wd p Fr (hfData r m pR pC lR lC)
      (hfVr r m p Fr VR) (hfVr r m p Fr VC) x y : ℕ) : ℚ) ≤ ρ x + γ y)
    (τ : ℕ) (hτ : (∑ x, ρ x) + (∑ y, γ y) ≤ (τ : ℚ)) :
    GLE p (τ + 2*(r-S.card)) (((altGeom g hg).family Fr depth).Q ⟨r,S⟩) := by
  subst m
  rw [altGeom_member_commonMinor g hg Fr depth hr S]
  apply member_gle hP (retainedFin (altGeom_hybShape g hg hr) S) ρ γ hρ hγ hf
  rw [card_retainedFin]
  push_cast
  linarith

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.alt_member_gle_of_dual
