module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The first `k` with `q ∣ k (4k - a)`, for `a ∈ {1, 3}` (generic for λ and the mirror)

`kqG a q = (jqG a q * q + a) / 4`, where `jqG a q = 1` if `q ≡ 4 - a (mod 4)` and `3` otherwise.
`kqG_le_of_dvd`: for an odd prime power `q` none of whose prime divisors divides `a`, every
`k ≥ 1` with `q ∣ k (4k - a)` satisfies `kqG a q ≤ k` and `q ≤ 4k - a`.

λ is `a = 1` and the mirror is `a = 3`.
-/

namespace CatalanCore.Arith

/-- `j_q = 1` if `q ≡ 4 - a (mod 4)`, `3` otherwise. -/
def jqG (a q : ℕ) : ℕ := if q % 4 = 4 - a then 1 else 3

/-- First `k ≥ 1` with `q ∣ k (4k - a)`. -/
def kqG (a q : ℕ) : ℕ := (jqG a q * q + a) / 4

lemma jqG_cases (a q : ℕ) : jqG a q = 1 ∨ jqG a q = 3 := by unfold jqG; split_ifs <;> simp

lemma kqG_le_of_dvd {a q k : ℕ} (ha : a = 1 ∨ a = 3) (hq : IsPrimePow q) (hqo : Odd q)
    (hna : ∀ p : ℕ, p.Prime → p ∣ q → ¬ p ∣ a) (hk : 0 < k) (hd : q ∣ k * (4 * k - a)) :
    kqG a q ≤ k ∧ q ≤ 4 * k - a := by
  have ha3 : a ≤ 3 := by omega
  have ha0 : 0 < a := by omega
  obtain ⟨p, e, hp0, he, rfl⟩ := hq
  have hp := hp0.nat_prime
  have hq2 : (p ^ e) % 2 = 1 := Nat.odd_iff.mp hqo
  have hpq : p ∣ p ^ e := dvd_pow_self p he.ne'
  have hcases : p ^ e ∣ k ∨ p ^ e ∣ 4 * k - a := by
    by_cases hpk : p ∣ k
    · left
      have : Nat.Coprime p (4 * k - a) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro h4
        have h5 : p ∣ 4 * k := Dvd.dvd.mul_left hpk 4
        have h6 : p ∣ a := by
          have := Nat.dvd_sub h5 h4
          have e1 : 4 * k - (4 * k - a) = a := by omega
          rwa [e1] at this
        exact hna p hp hpq h6
      exact (Nat.Coprime.pow_left e this).dvd_of_dvd_mul_right hd
    · right
      have : Nat.Coprime (p ^ e) k :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)
      exact this.dvd_of_dvd_mul_left hd
  rcases hcases with hc | hc
  · have := Nat.le_of_dvd hk hc
    unfold kqG jqG
    split_ifs <;> omega
  · obtain ⟨t, ht⟩ := hc
    have h4k : 4 * k - a = (p ^ e) * t := ht
    have hq4 : (p ^ e) % 4 = 1 ∨ (p ^ e) % 4 = 3 := by omega
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at h4k; omega
      · exact h0
    refine ⟨?_, ?_⟩
    · unfold kqG jqG
      by_cases hj : (p ^ e) % 4 = 4 - a
      · rw [if_pos hj]
        have : (p ^ e) ≤ (p ^ e) * t := Nat.le_mul_of_pos_right _ htpos
        omega
      · rw [if_neg hj]
        have hqa : (p ^ e) % 4 = a := by omega
        have hmul := Nat.mul_mod (p ^ e) t 4
        rw [hqa] at hmul
        have ht3 : t % 4 = 3 := by rcases ha with rfl | rfl <;> omega
        have h3t : 3 ≤ t := by omega
        have : (p ^ e) * 3 ≤ (p ^ e) * t := Nat.mul_le_mul_left _ h3t
        omega
    · rw [h4k]; exact Nat.le_mul_of_pos_right _ htpos

end CatalanCore.Arith
