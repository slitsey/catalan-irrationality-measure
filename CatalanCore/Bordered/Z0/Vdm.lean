module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring

/-!
# Z0.6: valuation of a Vandermonde product

If `X² ∣ τ i` on `S` and `X⁴ ∣ τ i - X²` on `C ⊆ S`, then `X^(2 C(|S|,2) + 2 C(|C|,2))`
divides `∏_{i<j} (τ j - τ i)`.
-/

@[expose] public section

open Finset

namespace CatalanCore.Bordered

open PowerSeries

variable {n : ℕ}

/-- Number of ordered pairs `i < j` inside `T`. -/
lemma pairs_eq_choose (T : Finset (Fin n)) :
    ∑ i : Fin n, ∑ j ∈ Ioi i, (if i ∈ T ∧ j ∈ T then 1 else 0) = T.card.choose 2 := by
  have hI : ∀ i : Fin n, Ioi i = univ.filter (fun j => i < j) := by
    intro i; ext j; simp
  simp only [hI, Finset.sum_filter]
  induction T using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ, Nat.choose_one_right, ← ih]
    have h1 : ∀ i j : Fin n, (if i < j then (if i ∈ insert a S ∧ j ∈ insert a S then 1 else 0) else 0)
        = (if i < j then (if i ∈ S ∧ j ∈ S then 1 else 0) else 0)
          + (if i = a then (if a < j ∧ j ∈ S then 1 else 0) else 0)
          + (if j = a then (if i < a ∧ i ∈ S then 1 else 0) else 0) := by
      intro i j
      by_cases hi : i = a
      · subst hi
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj, ha, Finset.mem_insert, ite_and]
      · by_cases hj : j = a
        · subst hj
          simp [hi, ha, Finset.mem_insert, ite_and]
        · simp [hi, hj, Finset.mem_insert, ite_and]
    simp only [h1, Finset.sum_add_distrib, ih]
    have e1 : ∑ x : Fin n, ∑ y : Fin n, (if x = a then (if a < y ∧ y ∈ S then 1 else 0) else 0)
        = (S.filter (fun y => a < y)).card := by
      rw [Finset.sum_eq_single a (by intro b _ hb; simp [hb]) (by simp)]
      simp only [if_true, Finset.sum_boole, Nat.cast_id]
      congr 1; ext y; simp [and_comm]
    have e2 : ∑ x : Fin n, ∑ y : Fin n, (if y = a then (if x < a ∧ x ∈ S then 1 else 0) else 0)
        = (S.filter (fun y => y < a)).card := by
      rw [Finset.sum_comm, Finset.sum_eq_single a (by intro b _ hb; simp [hb]) (by simp)]
      simp only [if_true, Finset.sum_boole, Nat.cast_id]
      congr 1; ext y; simp [and_comm]
    rw [e1, e2]
    have e3 : (S.filter (fun y => a < y)).card + (S.filter (fun y => y < a)).card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext y
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro hy
          have : y ≠ a := fun h => ha (h ▸ hy)
          rcases lt_or_gt_of_ne this with h | h
          · exact Or.inr ⟨hy, h⟩
          · exact Or.inl ⟨hy, h⟩
      · rw [Finset.disjoint_left]
        intro y h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact absurd (h1.2.trans h2.2) (lt_irrefl _)
    omega

/-- **Z0.6.** -/
theorem X_pow_dvd_vdm {R : Type*} [CommRing R] (τ : Fin n → R⟦X⟧) (S C : Finset (Fin n))
    (hCS : C ⊆ S) (hS : ∀ i ∈ S, (X : R⟦X⟧) ^ 2 ∣ τ i)
    (hC : ∀ i ∈ C, (X : R⟦X⟧) ^ 4 ∣ τ i - X ^ 2) :
    (X : R⟦X⟧) ^ (2 * S.card.choose 2 + 2 * C.card.choose 2)
      ∣ ∏ i, ∏ j ∈ Ioi i, (τ j - τ i) := by
  have hw : ∀ i : Fin n, ∀ j ∈ Ioi i,
      (X : R⟦X⟧) ^ (2 * (if i ∈ S ∧ j ∈ S then 1 else 0) + 2 * (if i ∈ C ∧ j ∈ C then 1 else 0))
        ∣ τ j - τ i := by
    intro i j _
    by_cases hc : i ∈ C ∧ j ∈ C
    · have hs : i ∈ S ∧ j ∈ S := ⟨hCS hc.1, hCS hc.2⟩
      simp only [hc, hs, and_self, if_true]
      have := dvd_sub (hC j hc.2) (hC i hc.1)
      rw [show τ j - X ^ 2 - (τ i - X ^ 2) = τ j - τ i by ring] at this
      exact this
    · by_cases hs : i ∈ S ∧ j ∈ S
      · simp only [hc, hs, and_self, if_true, if_false]
        exact dvd_sub (hS j hs.2) (hS i hs.1)
      · simp [hc, hs]
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
    Finset.prod_dvd_prod_of_dvd _ _ fun j hj => hw i j hj)
  simp only [Finset.prod_pow_eq_pow_sum]
  have : ∑ i : Fin n, ∑ j ∈ Ioi i, (2 * (if i ∈ S ∧ j ∈ S then 1 else 0)
      + 2 * (if i ∈ C ∧ j ∈ C then 1 else 0)) = 2 * S.card.choose 2 + 2 * C.card.choose 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, pairs_eq_choose]
  rw [← this]

end CatalanCore.Bordered
