module

public import CatalanCore.Uniform.Content.RankProducer.LineMember
public import CatalanCore.Uniform.Content.RankProducer.Restriction

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore.Uniform.Content.Hybrid
open scoped Classical

/-- Restricting killed coordinates loses at most the discarded cardinality of any label. -/
theorem filter_card_loss {α : Type*} [DecidableEq α] (A B : Finset α)
    (hB : B ⊆ A) (P : α → Prop) :
    (A.filter P).card ≤ (B.filter P).card + (A.card - B.card) := by
  have hsub : A.filter P ⊆ B.filter P ∪ (A \ B) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxB, (Finset.mem_filter.1 hx).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Finset.mem_filter.1 hx).1, hxB⟩)
  calc
    _ ≤ (B.filter P ∪ (A \ B)).card := Finset.card_le_card hsub
    _ ≤ (B.filter P).card + (A \ B).card := Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_sdiff_of_subset hB]

@[simp] theorem trim_rload (c : FibreCert) (kr kc : Finset ℕ) (d : ℕ) :
    (trim c kr kc).rload d = c.rload d := rfl

@[simp] theorem trim_cload (c : FibreCert) (kr kc : Finset ℕ) (d : ℕ) :
    (trim c kr kc).cload d = c.cload d := rfl

variable (p : ℕ) [Fact p.Prime]

/-- Removing row kills only removes annihilator constraints. -/
theorem lineMr_trim_mono (c : FibreCert) (kr kc : Finset ℕ) (hkr : kr ⊆ c.kr)
    (w : RatFunc (ZMod p) × RatFunc (ZMod p)) :
    lineMr p c w ≤ lineMr p (trim c kr kc) w := by
  by_cases h : ∀ d ∈ c.kr, omegaL (castV p (c.rload d)) w = 0
  · have ht : ∀ d ∈ (trim c kr kc).kr,
        omegaL (castV p ((trim c kr kc).rload d)) w = 0 := by
      intro d hd
      change omegaL (castV p (c.rload d)) w = 0
      exact h d (hkr hd)
    simp only [lineMr, if_pos h, if_pos ht] <;> exact le_rfl
  · rw [show lineMr p c w = 0 from if_neg h]
    exact Nat.zero_le _

#print axioms filter_card_loss
#print axioms lineMr_trim_mono
end CatalanCore.Uniform.Content.RankProducer
