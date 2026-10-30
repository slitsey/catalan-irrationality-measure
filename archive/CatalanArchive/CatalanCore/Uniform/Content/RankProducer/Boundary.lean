import CatalanCore.Uniform.Content.RankProducer.Geometry
import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer.Geometry
open Finset
open scoped Classical

/-- Residues touched by a deleted common node. -/
noncomputable def deletedResidues (r p : ℕ) (s : Finset (Fin r)) : Finset ℕ :=
  ((sᶜ : Finset (Fin r)).image Fin.val).image (fun n => n % p)

theorem deletedResidues_card (r p : ℕ) (s : Finset (Fin r)) :
    (deletedResidues r p s).card ≤ r - s.card := by
  calc _ ≤ ((sᶜ : Finset (Fin r)).image Fin.val).card := Finset.card_image_le
       _ ≤ (sᶜ : Finset (Fin r)).card := Finset.card_image_le
       _ = r - s.card := by simp [Finset.card_compl]

theorem kept_of_not_deleted (r p : ℕ) (s : Finset (Fin r)) (x : ℕ) (hx : x < p)
    (hgood : x ∉ deletedResidues r p s) :
    ∀ d : ℕ, x + p * d < r → keptN r s (x + p * d) := by
  intro d hd
  by_contra hk
  apply hgood
  have hs : (⟨x + p * d, hd⟩ : Fin r) ∉ s := fun hs => hk ⟨hd, hs⟩
  have hmod : (x + p * d) % p = x := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hx]
  exact Finset.mem_image.2 ⟨x + p * d,
    Finset.mem_image.2 ⟨⟨x + p * d, hd⟩, by simpa using hs, rfl⟩, hmod⟩

/-- Removing all deletion-touched residues loses at most the deletion depth. -/
theorem filter_not_deleted_card (r p : ℕ) (s : Finset (Fin r)) (A : Finset ℕ) :
    A.card ≤ (A.filter (fun x => x ∉ deletedResidues r p s)).card + (r - s.card) := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := A) (fun x => x ∉ deletedResidues r p s)
  have hsub : A.filter (fun x => ¬ x ∉ deletedResidues r p s) ⊆ deletedResidues r p s := by
    intro x hx
    exact not_not.mp (Finset.mem_filter.1 hx).2
  have hle := (Finset.card_le_card hsub).trans (deletedResidues_card r p s)
  omega

/-- A width-four strip about one rational affine boundary. -/
noncomputable def boundaryStrip (r p : ℕ) (D A B : ℤ) : Finset ℕ :=
  (range p).filter (fun x =>
    A * r + B * p - 4 * D ≤ D * x ∧ D * x ≤ A * r + B * p + 4 * D)

theorem boundaryStrip_card (r p : ℕ) (D A B : ℤ) (hD : 0 < D) :
    (boundaryStrip r p D A B).card ≤ 9 := by
  let S := boundaryStrip r p D A B
  by_cases hn : S.Nonempty
  · let v := S.min' hn
    have hv : v ∈ S := Finset.min'_mem S hn
    have hvlo := (Finset.mem_filter.1 hv).2.1
    have hsub : S ⊆ Icc v (v + 8) := by
      intro x hx
      have hmin : v ≤ x := Finset.min'_le S x hx
      have hxhi := (Finset.mem_filter.1 hx).2.2
      have hupper : (x : ℤ) ≤ v + 8 := by nlinarith
      exact Finset.mem_Icc.2 ⟨hmin, by exact_mod_cast hupper⟩
    calc S.card ≤ (Icc v (v + 8)).card := Finset.card_le_card hsub
         _ = 9 := by rw [Nat.card_Icc]; omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hn
    change S.card ≤ 9
    rw [he]
    simp

#print axioms deletedResidues_card
#print axioms kept_of_not_deleted
#print axioms boundaryStrip_card
end CatalanCore.Uniform.Content.RankProducer.Geometry
