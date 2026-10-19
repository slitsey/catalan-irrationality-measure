module

public import CatalanFrames.Lambda.ContentData
public import CatalanCore.Arith.Hybrid.SingLev
public import CatalanCore.Arith.Hybrid.Values
public import CatalanFrames.HybCommon.LogDhybT

@[expose] public section

/-!
# The λ instance of the generic hybrid layer (`HybCommon`)

`lamInst : HybInst lamFrame` is the block-valued instance (`HybInst.ofSing lamCD`), with
`Ebd N = 4 N²`; `kq q = (jq q · q + 1)/4` is attained, and the level of a prime is `0` exactly
below `kq`.  All λ-specific numerology (class `3 mod 4`: `k = (p+1)/4`; class `1 mod 4`:
`k = (3p+1)/4`) lives here and in `LambdaHybridContent`.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.Lambda

lemma lamPhi_le (k N : ℕ) (h : k ≤ N) : lamCD.Phi k ≤ 4 * N * N := by
  show k * (4 * k - 1) ≤ 4 * N * N
  calc k * (4 * k - 1) ≤ N * (4 * N) := Nat.mul_le_mul h (by omega)
    _ = 4 * N * N := by ring

/-- The block-valued hybrid instance of λ. -/
noncomputable def lamInst : HybInst lamFrame :=
  HybInst.ofSing lamCD (fun N => 4 * N * N) lamPhi_le

lemma lamInst_lev (q c : ℕ) : lamInst.lev q c = blk lamCD.Phi q c := rfl

lemma lam_4kq {q : ℕ} (hq2 : q % 2 = 1) (hq : 2 ≤ q) : 4 * kq q = jq q * q + 1 ∧ 0 < kq q := by
  unfold kq jq
  split_ifs with h <;> omega

lemma lam_kq_att (q : ℕ) (hq : IsPrimePow q) (hb : ∀ p ∈ lamCD.bad, ¬ p ∣ q) :
    0 < lamCD.kq q ∧ q ∣ lamCD.Phi (lamCD.kq q) := by
  have h2 : ¬ 2 ∣ q := hb 2 (by simp [lamCD])
  have hq2 : q % 2 = 1 := by omega
  have hq1 : 2 ≤ q := by
    obtain ⟨p, e, hp, he, rfl⟩ := hq
    have := hp.nat_prime.two_le
    calc 2 ≤ p := this
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  obtain ⟨h4, hpos⟩ := lam_4kq hq2 hq1
  refine ⟨hpos, ?_⟩
  show q ∣ kq q * (4 * kq q - 1)
  have : 4 * kq q - 1 = jq q * q := by omega
  rw [this]
  exact Dvd.dvd.mul_left (Dvd.intro_left _ rfl) _

lemma lam_lev_zero_iff {q c : ℕ} (hq : IsPrimePow q) (hb : ∀ p ∈ lamCD.bad, ¬ p ∣ q) :
    lamInst.lev q c = 0 ↔ c < lamCD.kq q := by
  rw [lamInst_lev]
  have := blk_pos_iff lamCD lam_kq_att (c := c) hq hb
  omega

lemma lam_lev_high (q c : ℕ) (hq : 1 ≤ q) (h : q ≤ c) : 0 < lamInst.lev q c := by
  rw [lamInst_lev]
  exact blk_pos_of (k := q) (Finset.mem_Icc.mpr ⟨hq, h⟩)
    (show q ∣ q * (4 * q - 1) from dvd_mul_right _ _)


lemma lam_kq_eq {p : ℕ} (h3 : p % 4 = 3) : lamCD.kq p = (p + 1) / 4 := by
  show kq p = _
  unfold kq jq; rw [if_pos h3]; simp

lemma lam_kq_eq1 {p : ℕ} (h1 : p % 4 = 1) : lamCD.kq p = (3 * p + 1) / 4 := by
  show kq p = _
  unfold kq jq; rw [if_neg (by omega)]

lemma lam_odd_good {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsPrimePow p ∧ (∀ q ∈ lamCD.bad, ¬ q ∣ p) := by
  refine ⟨hp.isPrimePow, ?_⟩
  intro q hq hd
  have : q = 2 := by simpa [lamCD] using hq
  subst this
  exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm

/-- **The tropical facts of λ**: `TropFacts lamInst 1` (offset `o = 1`). -/
theorem lam_tropFacts : TropFacts lamInst 1 where
  ho := Or.inl rfl
  kq3 := fun p hp h5 h => lam_kq_eq1 h
  kq1 := fun p hp h5 h => lam_kq_eq (by omega)
  good := fun p hp h5 => lam_odd_good hp (by omega)
  zero_iff := fun q c hq hb => lam_lev_zero_iff hq hb
  high := fun q c hq1 hqc => lam_lev_high q c hq1 hqc

lemma lam_cOf2 : cOf lamInst 2 = 4 := by
  show (16 : ℕ).factorization 2 = 4
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
  simp

lemma lam_cOf3 : cOf lamInst 3 = 0 :=
  cOf_eq_zero lamInst Nat.prime_three (by simp [lamInst, HybInst.ofSing, lamCD])

/-- **The bad-prime numerology of λ**: `BadInfo lamInst`. -/
theorem lam_badInfo : BadInfo lamInst where
  L4 := rfl
  Ebd4 := fun _ => rfl
  bad_sub := fun p hp => by simp_all [lamInst, HybInst.ofSing, lamCD]
  c2 := lam_cOf2
  c3 := lam_cOf3

end CatalanFrames.Lambda
