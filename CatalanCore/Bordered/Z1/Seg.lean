module

public import CatalanCore.Bordered.Z1.Tri3
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Eigenvector transfer between tridiagonal matrices with equal diagonal and equal products of
off-diagonal pairs, on a segment of indices.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

variable {F : Type*} [Field F] {n : ℕ}

theorem tri3_transfer (a d b a' b' : ℕ → F) (p q : ℕ) (lam : F)
    (hnz : ∀ i, p ≤ i → i + 1 < q → a i ≠ 0 ∧ a' i ≠ 0)
    (hprod : ∀ i, p ≤ i → i + 1 < q → a i * b i = a' i * b' i)
    (w : ℕ → F) (hsupp : ∀ k, k < p ∨ q ≤ k → w k = 0)
    (hne : ∃ k, p ≤ k ∧ k < q ∧ w k ≠ 0)
    (hw : ∀ k : Fin n, p ≤ (k : ℕ) → (k : ℕ) < q →
      (tri3 n a' d b' *ᵥ (fun j : Fin n => w j)) k = lam * w k) :
    ∃ w' : ℕ → F, (∀ k, k < p ∨ q ≤ k → w' k = 0) ∧ (∃ k, p ≤ k ∧ k < q ∧ w' k ≠ 0) ∧
      ∀ k : Fin n, p ≤ (k : ℕ) → (k : ℕ) < q →
        (tri3 n a d b *ᵥ (fun j : Fin n => w' j)) k = lam * w' k := by
  set S : ℕ → F := fun k => ∏ i ∈ Ico p k, a' i / a i with hS
  have hSsucc : ∀ k, p ≤ k → k + 1 < q → S (k + 1) = S k * (a' k / a k) := by
    intro k hk _
    simp only [hS]
    rw [Finset.prod_Ico_succ_top hk]
  have hSne : ∀ k, k < q → S k ≠ 0 := by
    intro k hk
    simp only [hS]
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := Finset.mem_Ico.1 hi
    obtain ⟨h1, h2⟩ := hnz i this.1 (by omega)
    exact div_ne_zero h2 h1
  refine ⟨fun k => S k * w k, fun k hk => by simp [hsupp k hk], ?_, ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := hne
    exact ⟨k, hk1, hk2, mul_ne_zero (hSne k hk2) hk3⟩
  · intro k hk1 hk2
    have h := hw k hk1 hk2
    rw [tri3_row a' d b' w k] at h
    show (tri3 n a d b *ᵥ (fun j : Fin n => (fun k => S k * w k) j)) k = lam * (S k * w k)
    rw [tri3_row a d b (fun k => S k * w k) k]
    have T2 : (if (k : ℕ) + 1 < n then a k * (S (k + 1) * w (k + 1)) else 0) =
        S k * (if (k : ℕ) + 1 < n then a' k * w (k + 1) else 0) := by
      by_cases hn : (k : ℕ) + 1 < n
      · simp only [hn, if_true]
        by_cases hq : (k : ℕ) + 1 < q
        · obtain ⟨h1, h2⟩ := hnz k hk1 hq
          rw [hSsucc k hk1 hq]
          field_simp
        · rw [hsupp (k + 1) (Or.inr (by omega))]; simp
      · simp [hn]
    have T3 : (if 0 < (k : ℕ) then b ((k : ℕ) - 1) * (S ((k : ℕ) - 1) * w ((k : ℕ) - 1)) else 0) =
        S k * (if 0 < (k : ℕ) then b' ((k : ℕ) - 1) * w ((k : ℕ) - 1) else 0) := by
      by_cases h0 : 0 < (k : ℕ)
      · simp only [h0, if_true]
        by_cases hp : p ≤ (k : ℕ) - 1
        · have hq : (k : ℕ) - 1 + 1 < q := by omega
          obtain ⟨h1, h2⟩ := hnz _ hp hq
          have hpr := hprod _ hp hq
          have e := hSsucc _ hp hq
          rw [show (k : ℕ) - 1 + 1 = k by omega] at e
          rw [e]
          field_simp
          linear_combination (S ((k : ℕ) - 1) * w ((k : ℕ) - 1)) * hpr
        · rw [hsupp ((k : ℕ) - 1) (Or.inl (by omega))]; simp
      · simp [h0]
    rw [T2, T3]
    linear_combination (S k) * h

end CatalanCore.Bordered.Z1
