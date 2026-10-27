module
public import CatalanCore.Rect.CharZeroNV.Wronskian
@[expose] public section
/-! Step-component counts: a finite subset of the natural numbers is a disjoint
union of step-L chains. Its terminal nodes count those chains. -/
open Finset Polynomial
namespace CatalanCore.Uniform.NV

def stepEdges (Z : Finset ℕ) (L : ℕ) : Finset ℕ := Z.filter (fun a => a+L ∈ Z)
def stepEnds (Z : Finset ℕ) (L : ℕ) : Finset ℕ := Z.filter (fun a => a+L ∉ Z)
def componentCount (Z : Finset ℕ) (L : ℕ) : ℕ := (stepEnds Z L).card

@[simp] theorem mem_stepEdges {Z : Finset ℕ} {L a : ℕ} :
    a ∈ stepEdges Z L ↔ a ∈ Z ∧ a+L ∈ Z := by simp [stepEdges]
@[simp] theorem mem_stepEnds {Z : Finset ℕ} {L a : ℕ} :
    a ∈ stepEnds Z L ↔ a ∈ Z ∧ a+L ∉ Z := by simp [stepEnds]

theorem card_edges_add_components (Z : Finset ℕ) (L : ℕ) :
    (stepEdges Z L).card + componentCount Z L = Z.card := by
  simpa [stepEdges,componentCount,stepEnds] using
    Finset.card_filter_add_card_filter_not (s := Z) (p := fun a => a+L ∈ Z)

theorem card_stepEdges (Z : Finset ℕ) (L : ℕ) :
    (stepEdges Z L).card = Z.card - componentCount Z L := by
  have := card_edges_add_components Z L
  omega

theorem stepEdges_mono {C Z : Finset ℕ} (h : C ⊆ Z) (L : ℕ) :
    stepEdges C L ⊆ stepEdges Z L := by
  intro a ha
  rcases mem_stepEdges.mp ha with ⟨ha,hb⟩
  exact mem_stepEdges.mpr ⟨h ha,h hb⟩

/-- Every node belongs to a step chain ending at a terminal node. -/
theorem exists_terminal (Z : Finset ℕ) (L : ℕ) (hL : 0 < L) (a : ℕ) (ha : a ∈ Z) :
    ∃ b ∈ stepEnds Z L, ∃ j : ℕ, b = a+j*L := by
  have hex : ∃ j : ℕ, a+j*L ∉ Z := by
    refine ⟨Z.sup id+1, ?_⟩
    intro hin
    have hbound : a+(Z.sup id+1)*L ≤ Z.sup id := Finset.le_sup (f := id) hin
    have hmul : Z.sup id+1 ≤ (Z.sup id+1)*L := Nat.le_mul_of_pos_right _ hL
    omega
  let j := Nat.find hex
  have hj : a+j*L ∉ Z := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    have hnot : a ∉ Z := by simpa [hz] using hj
    exact hnot ha
  have hprev : a+(j-1)*L ∈ Z := by
    by_contra hn
    exact Nat.find_min hex (by omega) hn
  refine ⟨a+(j-1)*L, mem_stepEnds.mpr ⟨hprev, ?_⟩, j-1, rfl⟩
  have he : a+(j-1)*L+L = a+j*L := by
    calc
      a+(j-1)*L+L = a+((j-1)+1)*L := by ring
      _ = a+j*L := by rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
  simpa only [he] using hj

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
noncomputable def fieldNodes (Z : Finset ℕ) : Finset K := Z.image (fun a : ℕ => (a : K))
@[simp] theorem card_fieldNodes (Z : Finset ℕ) : (fieldNodes Z : Finset K).card = Z.card := by
  classical
  exact Finset.card_image_of_injective Z (Nat.cast_injective (R := K))

theorem fieldNodes_mono {C Z : Finset ℕ} (h : C ⊆ Z) :
    (fieldNodes C : Finset K) ⊆ fieldNodes Z := by
  classical
  exact Finset.image_subset_image h

/-- The concrete step roots supply the component debit in the root count. -/
theorem degree_ge_step_roots (Z C : Finset ℕ) (hCZ : C ⊆ Z) (L : ℕ)
    (W : K[X]) (hW : W ≠ 0)
    (hv : ∀ a ∈ stepEdges Z L, W.eval (a : K) = 0)
    (hj : ∀ a ∈ stepEdges C L, W.derivative.eval (a : K) = 0) :
    Z.card-componentCount Z L + (C.card-componentCount C L) ≤ W.natDegree := by
  classical
  by_contra hn
  apply hW
  apply CatalanCore.Rect.CharZeroNV.eq_zero_of_hermite_roots
    (fieldNodes (stepEdges Z L)) (fieldNodes (stepEdges C L))
    (fieldNodes_mono (stepEdges_mono hCZ L)) W
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact hv a ha
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact hj a ha
  · simpa only [card_fieldNodes,card_stepEdges] using (Nat.lt_of_not_ge hn)
end CatalanCore.Uniform.NV



