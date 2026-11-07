module

public import CatalanFrames.HybCommon.DefAll
public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# The dual excess `eNG` as an explicit linear expression (generic in the offset)

`dualBG_eq`: the D4 dual value is `2 (r - k) + 4m - (p - r)`.  `eNG_cases`: `eNG` is `0` or one of the
six explicit linear expressions (one per window); every extended-weight cover is then an `omega`
problem.
-/

open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {o r p : ℕ}

lemma dualBG_eq (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (hW : WBG r p) :
    dualBG o r (r / 8) p = 2 * (r - kBG o p) + 4 * (r / 8) - (p - r) := by
  obtain ⟨hp, h1, h2⟩ := hW
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2' : 2 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
    omega
  have hkB : kBG o p ≤ r := by
    unfold kBG; rcases ho with rfl | rfl <;> split_ifs <;> omega
  unfold dualBG
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hrow : ∑ c : Fin r, uPot p r (kBG o p) (Frame.hybRow r (r / 8) (Sum.inl c)) =
      r - kBG o p := by
    have : ∀ c : Fin r, uPot p r (kBG o p) (Frame.hybRow r (r / 8) (Sum.inl c)) =
        if kBG o p ≤ (c : ℕ) then 1 else 0 := fun c => by
      show uPot p r (kBG o p) (c : ℕ) = _
      unfold uPot; rw [if_pos c.2]
    simp only [this]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if kBG o p ≤ i then 1 else 0) r]
    exact sum_range_le_ind r (kBG o p)
  have hcol : ∑ c : Fin r, uPot p r (kBG o p) (Frame.hybCol r (r / 8) (Sum.inl c)) =
      r - kBG o p := hrow
  have hzr : ∑ i : Fin (r / 8), uPot p r (kBG o p) (Frame.hybRow r (r / 8) (Sum.inr i)) =
      (r / 8) + ((r / 8) - (p - r + 1) / 2) := by
    have : ∀ i : Fin (r / 8), uPot p r (kBG o p) (Frame.hybRow r (r / 8) (Sum.inr i)) =
        1 + (if (p - r + 1) / 2 ≤ (i : ℕ) then 1 else 0) := fun i => by
      show uPot p r (kBG o p) (r + 2 * (i : ℕ)) = _
      unfold uPot
      rw [if_neg (by omega)]
      by_cases h : p ≤ r + 2 * (i : ℕ)
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    simp only [this]
    rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      if (p - r + 1) / 2 ≤ i then 1 else 0) (r / 8), sum_range_le_ind]
    simp
  have hzc : ∑ i : Fin (r / 8), uPot p r (kBG o p) (Frame.hybCol r (r / 8) (Sum.inr i)) =
      (r / 8) + ((r / 8) - (p - r) / 2) := by
    have : ∀ i : Fin (r / 8), uPot p r (kBG o p) (Frame.hybCol r (r / 8) (Sum.inr i)) =
        1 + (if (p - r) / 2 ≤ (i : ℕ) then 1 else 0) := fun i => by
      show uPot p r (kBG o p) (r + 2 * (i : ℕ) + 1) = _
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

/-- `eNG` is `0` or one of six explicit expressions, according to the window. -/
lemma eNG_cases (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) :
    eNG o r p = 0 ∨
    (cleanE1G o r p ∧ eNG o r p = 2 * ((r - p) + (r - (3 * p + o) / 4)) + 4 * (r / 8)) ∨
    (cleanE3G o r p ∧ eNG o r p = 2 * r + r / 8) ∨
    (WBG r p ∧ eNG o r p = 2 * (r - kBG o p) + 4 * (r / 8) - (p - r)) ∨
    (WC5G o r p ∧ eNG o r p = 2 * r + 2 * (r / 8) - (p + (p + o) / 4 - r)) ∨
    (WC7G o r p ∧ eNG o r p = 2 * r + 2 * (r / 8) - (p + (3 * p + o) / 4 - r)) ∨
    (LowCleanO o r (r / 8) p ∧ eNG o r p = 2 * r + r / 8) := by
  by_cases hl : LowCleanO o r (r / 8) p
  · right; right; right; right; right; right
    obtain ⟨n1, n2, n3, n4, n5⟩ := disj_lc ho hr hl
    refine ⟨hl, ?_⟩
    simp [eNG, hl, n1, n2, n3, n4, n5]
  by_cases h7 : WC7G o r p
  · right; right; right; right; right; left
    obtain ⟨n1, n2, n3, n4⟩ := disj_c7 ho hr h7
    refine ⟨h7, ?_⟩
    simp [eNG, hl, h7, n1, n2, n3, n4]
  by_cases h5 : WC5G o r p
  · right; right; right; right; left
    obtain ⟨n1, n2, n3⟩ := disj_c5 ho hr h5
    refine ⟨h5, ?_⟩
    simp [eNG, hl, h7, h5, n1, n2, n3]
  by_cases hB : WBG r p
  · right; right; right; left
    obtain ⟨n1, n2⟩ := disj_b ho hr hB
    refine ⟨hB, ?_⟩
    rw [← dualBG_eq ho hr hB]
    simp [eNG, hl, h7, h5, hB, n1, n2]
  by_cases h3 : cleanE3G o r p
  · right; right; left
    have n1 := disj_e3 ho hr h3
    refine ⟨h3, ?_⟩
    simp [eNG, hl, h7, h5, hB, h3, n1]
  by_cases h1 : cleanE1G o r p
  · right; left
    refine ⟨h1, ?_⟩
    simp [eNG, hl, h7, h5, hB, h3, h1, dualE1G]
  · left
    simp [eNG, hl, h7, h5, hB, h3, h1]

lemma kBG_j1 (ho : o = 1 ∨ o = 3) (hm : p % 4 = 4 - o) : kBG o p = (p + o) / 4 := by
  unfold kBG; rw [if_neg (by rcases ho with rfl | rfl <;> omega)]

lemma kBG_j3 (hm : p % 4 = o) : kBG o p = (3 * p + o) / 4 := by
  unfold kBG; rw [if_pos hm]

end CatalanFrames.HybCommon
