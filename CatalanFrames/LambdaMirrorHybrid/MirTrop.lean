module

public import CatalanFrames.LambdaMirrorHybrid.MirInst
public import CatalanFrames.HybCommon.Trop

@[expose] public section

/-!
# The mirror tropical facts: `TropFacts mirNInst 3`

`kq p = (p + 3)/4` for `p ≡ 1 (4)` (class `j = 1`), `(3p + 3)/4` for `p ≡ 3 (4)` (class `j = 3`);
the bad primes are `{2, 3}`.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror
  CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

lemma mir_kq_att (q : ℕ) (hq : IsPrimePow q) (hb : ∀ p ∈ mirCD.bad, ¬ p ∣ q) :
    0 < mirCD.kq q ∧ q ∣ mirCD.Phi (mirCD.kq q) := by
  have h2 : ¬ 2 ∣ q := hb 2 (by simp [mirCD])
  have h3 : ¬ 3 ∣ q := hb 3 (by simp [mirCD])
  have hq1 : 2 ≤ q := by
    obtain ⟨p, e, hp, he, rfl⟩ := hq
    have := hp.nat_prime.two_le
    calc 2 ≤ p := this
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hq2 : q % 2 = 1 := by omega
  have hkq : mirCD.kq q = (jq q * q + 3) / 4 := rfl
  have h4 : 4 * mirCD.kq q = jq q * q + 3 := by
    rw [hkq]; unfold jq; split_ifs with h <;> omega
  have hpos : 0 < mirCD.kq q := by
    rw [hkq]; unfold jq; split_ifs <;> omega
  refine ⟨hpos, ?_⟩
  show q ∣ mirCD.kq q * (4 * mirCD.kq q - 3)
  have : 4 * mirCD.kq q - 3 = jq q * q := by omega
  rw [this]
  exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _

theorem mirN_tropFacts : TropFacts mirNInst 3 where
  ho := Or.inr rfl
  kq3 := fun p hp h5 h => by
    show (jq p * p + 3) / 4 = (3 * p + 3) / 4
    unfold jq; rw [if_neg (by omega)]
  kq1 := fun p hp h5 h => by
    show (jq p * p + 3) / 4 = (p + 3) / 4
    unfold jq; rw [if_pos (by omega)]; simp
  good := fun p hp h5 => ⟨hp.isPrimePow, fun q hq hd => by
    simp only [mirNInst, mirInst, HybInst.neg, HybInst.ofSing, ContentData.neg, mirCD,
      Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd; omega⟩
  zero_iff := fun q c hq hb => by
    have := blk_pos_iff mirCD mir_kq_att (c := c) hq hb
    show blk mirCD.Phi q c = 0 ↔ c < mirCD.kq q
    omega
  high := fun q c hq1 hqc => by
    show 0 < blk mirCD.Phi q c
    exact blk_pos_of (k := q) (Finset.mem_Icc.mpr ⟨hq1, hqc⟩)
      (show q ∣ q * (4 * q - 3) from dvd_mul_right _ _)

end CatalanFrames.LambdaMirrorHybrid
