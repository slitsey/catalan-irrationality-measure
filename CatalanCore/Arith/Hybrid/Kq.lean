module

public import CatalanCore.Arith.Hybrid.Levels

@[expose] public section

/-!
# The first singular index of a prime `p ≥ 5`

`kq p = (p+1)/4` for `p ≡ 3 (4)` and `(3p+1)/4` for `p ≡ 1 (4)`; `blk p c > 0 ↔ kq p ≤ c`.
This turns the potentials of `Dual.lean` (`[0 < blk]`) into explicit counts.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

/-- The least `p`-singular index: `4 kq - 1 = j p`, `j ∈ {1, 3}`. -/
def kq (p : ℕ) : ℕ := if p % 4 = 3 then (p + 1) / 4 else (3 * p + 1) / 4

lemma kq_sing {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Sing p (kq p) := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  unfold Sing kq
  by_cases h3 : p % 4 = 3
  · rw [if_pos h3]
    have : 4 * ((p + 1) / 4) - 1 = p := by omega
    rw [this]; exact dvd_mul_left _ _
  · rw [if_neg h3]
    have : 4 * ((3 * p + 1) / 4) - 1 = 3 * p := by omega
    rw [this]; exact Dvd.dvd.mul_left (dvd_mul_left _ _) _

lemma kq_pos {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 1 ≤ kq p := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have := hp.two_le
  unfold kq; split_ifs <;> omega

lemma kq_le_of_sing {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hk : 1 ≤ k) (hs : Sing p k) :
    kq p ≤ k := by
  have hodd := hp.eq_two_or_odd.resolve_left h2
  have hp2 := hp.two_le
  unfold Sing at hs
  have hc : kq p < p := by unfold kq; split_ifs <;> omega
  rcases (Nat.Prime.dvd_mul hp).mp hs with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · obtain ⟨t, ht⟩ := h
    have ht0 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; omega
      · exact h0
    unfold kq
    split_ifs with h3
    · have : p * 1 ≤ p * t := Nat.mul_le_mul_left _ ht0
      omega
    · by_cases t1 : t = 1
      · subst t1; omega
      · by_cases t2 : t = 2
        · subst t2; omega
        · have : p * 3 ≤ p * t := Nat.mul_le_mul_left _ (by omega)
          omega

theorem blk_pos_iff {p c : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 0 < blk p c ↔ kq p ≤ c := by
  constructor
  · intro h
    unfold blk at h
    obtain ⟨k, hk⟩ := Finset.card_pos.mp h
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    have := Finset.mem_Icc.mp hk1
    exact (kq_le_of_sing hp h2 this.1 hk2).trans this.2
  · intro h
    exact blk_pos_of (k := kq p) (Finset.mem_Icc.mpr ⟨kq_pos hp h2, h⟩) (kq_sing hp h2)

end CatalanCore.Arith.Hybrid
