module

public import CatalanFrames.Lambda.HybDefAll
public import CatalanFrames.Lambda.HybContent8

@[expose] public section

/-!
# λ: the content bound for the deficit family (`DhybT`), part 1: the dual excess `eN`

`dualB_eq`: the dual value of the D4 potentials is `2 (r - k) + 4m - (p - r)` exactly.
`eN_arith`: `eN` is `0`, or one of three explicit linear expressions (class 1 window, class 3
window, B window), so that every piece-bound check is an `omega` problem.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma sum_range_le_ind (n k : ℕ) :
    ∑ i ∈ Finset.range n, (if k ≤ i then 1 else 0) = n - k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : k ≤ n
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

lemma dualB_eq {r p : ℕ} (hr : 16 ≤ r) (hW : WB r p) :
    dualB r (r / 8) p = 2 * (r - kB p) + 4 * (r / 8) - (p - r) := by
  obtain ⟨hp, h1, h2⟩ := hW
  have hkB : kB p ≤ r := by
    unfold kB; split_ifs <;> omega
  unfold dualB
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hrow : ∑ c : Fin r, uPot p r (kB p) (Frame.hybRow r (r / 8) (Sum.inl c)) = r - kB p := by
    have : ∀ c : Fin r, uPot p r (kB p) (Frame.hybRow r (r / 8) (Sum.inl c)) =
        if kB p ≤ (c : ℕ) then 1 else 0 := fun c => by
      show uPot p r (kB p) (c : ℕ) = _
      unfold uPot; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if kB p ≤ i then 1 else 0) r]
    exact sum_range_le_ind r (kB p)
  have hcol : ∑ c : Fin r, uPot p r (kB p) (Frame.hybCol r (r / 8) (Sum.inl c)) = r - kB p := hrow
  have hzr : ∑ i : Fin (r / 8), uPot p r (kB p) (Frame.hybRow r (r / 8) (Sum.inr i)) =
      (r / 8) + ((r / 8) - (p - r + 1) / 2) := by
    have : ∀ i : Fin (r / 8), uPot p r (kB p) (Frame.hybRow r (r / 8) (Sum.inr i)) =
        1 + (if (p - r + 1) / 2 ≤ (i : ℕ) then 1 else 0) := fun i => by
      show uPot p r (kB p) (r + 2 * (i : ℕ)) = _
      unfold uPot
      rw [if_neg (by omega)]
      by_cases h : p ≤ r + 2 * (i : ℕ)
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      if (p - r + 1) / 2 ≤ i then 1 else 0) (r / 8), sum_range_le_ind]
    simp
  have hzc : ∑ i : Fin (r / 8), uPot p r (kB p) (Frame.hybCol r (r / 8) (Sum.inr i)) =
      (r / 8) + ((r / 8) - (p - r) / 2) := by
    have : ∀ i : Fin (r / 8), uPot p r (kB p) (Frame.hybCol r (r / 8) (Sum.inr i)) =
        1 + (if (p - r) / 2 ≤ (i : ℕ) then 1 else 0) := fun i => by
      show uPot p r (kB p) (r + 2 * (i : ℕ) + 1) = _
      unfold uPot
      rw [if_neg (by omega)]
      by_cases h : p ≤ r + 2 * (i : ℕ) + 1
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      if (p - r) / 2 ≤ i then 1 else 0) (r / 8), sum_range_le_ind]
    simp
  rw [hrow, hcol, hzr, hzc]
  omega

lemma eN_arith (r p : ℕ) (hr : 16 ≤ r) (hp : p.Prime) :
    eN r p = 0 ∨
    (p % 4 = 1 ∧ 5 * r + 8 ≤ 7 * p ∧ p < r ∧
      eN r p = 2 * ((r - p) + (r - (3 * p + 1) / 4)) + 4 * (r / 8)) ∨
    (p % 4 = 3 ∧ 5 * r + 8 ≤ 8 * p ∧ 5 * p + 5 ≤ 4 * r ∧ eN r p = 2 * r + r / 8) ∨
    (r < p ∧ p < r + r / 8 ∧
      ((p % 4 = 1 ∧ eN r p = 2 * (r - (3 * p + 1) / 4) + 4 * (r / 8) - (p - r)) ∨
       (p % 4 = 3 ∧ eN r p = 2 * (r - (p + 1) / 4) + 4 * (r / 8) - (p - r)))) := by
  classical
  by_cases h1 : cleanE1 r p
  · right; left
    obtain ⟨_, h4, h7, hpr⟩ := id h1
    have n3 : ¬ cleanE3 r p := fun h => by have := h.2.1; omega
    have nB : ¬ WB r p := fun h => by have := h.2.1; omega
    refine ⟨h4, h7, hpr, ?_⟩
    simp [eN, dualE1, h1, n3, nB]
  · by_cases h3 : cleanE3 r p
    · right; right; left
      obtain ⟨_, h4, h8, h5, _⟩ := id h3
      have nB : ¬ WB r p := fun h => by have := h.2.1; omega
      refine ⟨h4, h8, h5, ?_⟩
      simp [eN, h1, h3, nB]
    · by_cases hB : WB r p
      · right; right; right
        have hd := dualB_eq hr hB
        have hodd : p % 2 = 1 := by
          by_contra h
          have h2' : 2 ∣ p := by omega
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
          have := hB.2.1; omega
        refine ⟨hB.2.1, hB.2.2, ?_⟩
        have e : eN r p = dualB r (r / 8) p := by simp [eN, h1, h3, hB]
        rw [e, hd]
        by_cases h4 : p % 4 = 1
        · left; refine ⟨h4, ?_⟩; unfold kB; rw [if_pos h4]
        · right; refine ⟨by omega, ?_⟩; unfold kB; rw [if_neg h4]
      · left; simp [eN, h1, h3, hB]

end CatalanFrames.Lambda
