import CatalanCore.Uniform.Bank.Lambda.RunCount
import CatalanCore.Uniform.Content.RankProducer.Counts
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open Finset
open scoped Classical

/-- The good physical run, represented in the residue-field index type. -/
noncomputable def goodRunFibres (r p res : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (a b : ℚ) : Finset (ZMod p) :=
  univ.filter (fun x => x.val ∈ (runResidues p res a b).filter
    (fun y => y ∉ deletedResidues r p s))

theorem goodRunFibres_card (r p res : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (a b : ℚ) :
    (goodRunFibres r p res s a b).card =
      ((runResidues p res a b).filter (fun y => y ∉ deletedResidues r p s)).card := by
  have himage : (goodRunFibres r p res s a b).image ZMod.val =
      (runResidues p res a b).filter (fun y => y ∉ deletedResidues r p s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact (Finset.mem_filter.1 hy).2
    · intro hx
      have hxp : x < p := Finset.mem_range.1
        (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).1
      have hv : (x : ZMod p).val = x := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hxp]
      refine Finset.mem_image.2 ⟨(x : ZMod p), ?_, hv⟩
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_univ _, by simpa only [hv] using hx⟩
  calc
    _ = ((goodRunFibres r p res s a b).image ZMod.val).card :=
      (Finset.card_image_of_injective _ (ZMod.val_injective p)).symm
    _ = _ := congrArg Finset.card himage

/-- A certified positive contribution on the physical run gives its affine mass,
with only the fixed boundary and common-deletion losses. -/
theorem goodRunFibres_sum_lower (r p res : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (a b : ℚ) (hres : res = 0 ∨ res = 1)
    (ha : 0 ≤ a) (hb : b ≤ p) (f : ZMod p → ℕ)
    (hf : ∀ x ∈ goodRunFibres r p res s a b, 1 ≤ f x) :
    (b - a) / 2 - 6 - ((r - s.card : ℕ) : ℚ) ≤ ∑ x, (f x : ℚ) := by
  have hn : (goodRunFibres r p res s a b).card ≤ ∑ x, f x := by
    calc
      _ = ∑ _x ∈ goodRunFibres r p res s a b, 1 := by simp
      _ ≤ ∑ x ∈ goodRunFibres r p res s a b, f x := Finset.sum_le_sum hf
      _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hq : ((goodRunFibres r p res s a b).card : ℚ) ≤ ∑ x, (f x : ℚ) := by
    exact_mod_cast hn
  rw [goodRunFibres_card] at hq
  exact (good_runResidues_card_lower r p res s a b hres ha hb).trans hq

/-- Upper count on the same residue-field set, including deletion filtering. -/
theorem goodRunFibres_card_upper (r p res : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (a b : ℚ) (hres : res = 0 ∨ res = 1) (hab : a ≤ b) :
    ((goodRunFibres r p res s a b).card : ℚ) ≤ (b - a) / 2 + 6 := by
  rw [goodRunFibres_card]
  have hsub := Finset.filter_subset (fun y => y ∉ deletedResidues r p s) (runResidues p res a b)
  have hcard : (((runResidues p res a b).filter
      (fun y => y ∉ deletedResidues r p s)).card : ℚ) ≤ ((runResidues p res a b).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (runResidues_card_upper p res a b hres hab)

/-- Both bounds on a good run use only a fixed error and common-deletion depth. -/
theorem goodRunFibres_card_bounds (r p res : ℕ) [Fact p.Prime]
    (s : Finset (Fin r)) (a b : ℚ) (hres : res = 0 ∨ res = 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ p) :
    (b - a) / 2 - 6 - ((r - s.card : ℕ) : ℚ) ≤ (goodRunFibres r p res s a b).card ∧
      ((goodRunFibres r p res s a b).card : ℚ) ≤ (b - a) / 2 + 6 := by
  constructor
  · rw [goodRunFibres_card]
    exact good_runResidues_card_lower r p res s a b hres ha hb
  · exact goodRunFibres_card_upper r p res s a b hres hab

#print axioms goodRunFibres_card
#print axioms goodRunFibres_card_bounds
#print axioms goodRunFibres_sum_lower
end CatalanCore.Uniform.Bank.Lambda
