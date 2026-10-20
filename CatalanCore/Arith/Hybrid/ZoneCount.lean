module

public import CatalanCore.Arith.Hybrid.ClassAssignment
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # Counting a single interval in the interlaced zone

The even rows and odd columns partition the physical zone exactly.  One
interval potential therefore replaces separate parity and floor counts.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

def zoneLabel (r m : ℕ) : Fin m ⊕ Fin m → ℕ :=
  Sum.elim (fun i => r + 2 * (i : ℕ)) (fun j => r + 2 * (j : ℕ) + 1)

theorem sum_zone {K : Type*} [AddCommMonoid K] (r m : ℕ) (f : ℕ → K) :
    (∑ i : Fin m, f (r + 2 * (i : ℕ))) +
      (∑ j : Fin m, f (r + 2 * (j : ℕ) + 1)) = ∑ z ∈ Ico r (r + 2 * m), f z := by
  have hs : (∑ i : Fin m ⊕ Fin m, f (zoneLabel r m i)) =
      ∑ z ∈ Ico r (r + 2 * m), f z := by
    apply Finset.sum_bij (fun i _ => zoneLabel r m i)
    · intro i _
      cases i with
      | inl i => have := i.isLt; simp only [zoneLabel, Sum.elim_inl, mem_Ico]; omega
      | inr i => have := i.isLt; simp only [zoneLabel, Sum.elim_inr, mem_Ico]; omega
    · intro i _ j _ hij
      cases i with
      | inl i => cases j with
        | inl j => apply congrArg Sum.inl; apply Fin.ext; simp only [zoneLabel, Sum.elim_inl] at hij; omega
        | inr j => simp only [zoneLabel, Sum.elim_inl, Sum.elim_inr] at hij; omega
      | inr i => cases j with
        | inl j => simp only [zoneLabel, Sum.elim_inl, Sum.elim_inr] at hij; omega
        | inr j => apply congrArg Sum.inr; apply Fin.ext; simp only [zoneLabel, Sum.elim_inr] at hij; omega
    · intro z hz
      have hz' := mem_Ico.mp hz
      have hi : (z-r)/2 < m := by omega
      by_cases he : (z-r)%2=0
      · exact ⟨Sum.inl ⟨(z-r)/2, hi⟩, mem_univ _, by simp only [zoneLabel, Sum.elim_inl]; omega⟩
      · exact ⟨Sum.inr ⟨(z-r)/2, hi⟩, mem_univ _, by simp only [zoneLabel, Sum.elim_inr]; omega⟩
    · intro i _; rfl
  simpa only [Fintype.sum_sum_type, zoneLabel, Sum.elim_inl, Sum.elim_inr] using hs

/-- The one-sided interval dual: the vertices in `[a,b)` have cost zero. -/
def intervalCost (a b z : ℕ) : ℕ := if a ≤ z ∧ z < b then 0 else 1

theorem sum_intervalCost (r m a b : ℕ) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b ≤ r + 2 * m) :
    (∑ i : Fin m, intervalCost a b (r+2*(i:ℕ))) +
      (∑ j : Fin m, intervalCost a b (r+2*(j:ℕ)+1)) = 2*m-(b-a) := by
  rw [sum_zone]
  have he : (Ico r (r+2*m)).filter (fun z => ¬(a ≤ z ∧ z < b)) =
      Ico r a ∪ Ico b (r+2*m) := by
    ext z
    simp only [mem_filter, mem_Ico, mem_union]
    omega
  have hd : Disjoint (Ico r a) (Ico b (r+2*m)) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    have := mem_Ico.mp h1
    have := mem_Ico.mp h2
    omega
  have hs : (∑ z ∈ Ico r (r+2*m), intervalCost a b z) =
      ((Ico r (r+2*m)).filter (fun z => ¬(a ≤ z ∧ z < b))).card := by
    have hc : ∀ z, intervalCost a b z = if ¬(a ≤ z ∧ z < b) then 1 else 0 := by
      intro z; by_cases h : a ≤ z ∧ z < b <;> simp [intervalCost, h]
    simp_rw [hc]
    rw [← Finset.sum_filter]
    simp
  rw [hs, he, card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico]
  omega

/-- The assignment bound from a zero rectangle whose incident entries cost at
most one.  The surrounding entries may cost two. -/
theorem interval_assignment_bound (r m a b : ℕ) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b ≤ r+2*m) (W : Fin m → Fin m → ℕ)
    (h2 : ∀ i j, W i j ≤ 2)
    (h0 : ∀ i j : Fin m, a ≤ r+2*(i:ℕ) → r+2*(i:ℕ) < b →
      a ≤ r+2*(j:ℕ)+1 → r+2*(j:ℕ)+1 < b → W i j=0)
    (hrow : ∀ i j : Fin m, a ≤ r+2*(i:ℕ) → r+2*(i:ℕ) < b → W i j≤1)
    (hcol : ∀ i j : Fin m, a ≤ r+2*(j:ℕ)+1 → r+2*(j:ℕ)+1 < b → W i j≤1) :
    tropVal W ≤ 2*m-(b-a) := by
  have h := tropVal_le_nat_dual W
    (fun i => intervalCost a b (r+2*(i:ℕ)))
    (fun j => intervalCost a b (r+2*(j:ℕ)+1)) (by
      intro i j
      by_cases hi : a ≤ r+2*(i:ℕ) ∧ r+2*(i:ℕ)<b <;>
        by_cases hj : a ≤ r+2*(j:ℕ)+1 ∧ r+2*(j:ℕ)+1<b
      · simp only [intervalCost, if_pos hi, if_pos hj, zero_add]
        exact (h0 i j hi.1 hi.2 hj.1 hj.2).le
      · simpa only [intervalCost, if_pos hi, if_neg hj, zero_add] using hrow i j hi.1 hi.2
      · simpa only [intervalCost, if_neg hi, if_pos hj, add_zero] using hcol i j hj.1 hj.2
      · simpa only [intervalCost, if_neg hi, if_neg hj] using h2 i j)
  rwa [sum_intervalCost r m a b hra hab hb] at h

end CatalanCore.Arith.Hybrid
