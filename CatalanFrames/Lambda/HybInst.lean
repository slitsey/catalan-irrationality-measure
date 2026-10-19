module

public import CatalanFrames.Lambda.ContentData
public import CatalanCore.Arith.Hybrid.SingLev
public import CatalanCore.Arith.Hybrid.Values

@[expose] public section

/-!
# The λ instance of the hybrid content machinery (thin)

`lamInst : HybInst lamFrame` is the block-valued instance (`HybInst.ofSing lamCD`), with
`Ebd N = 4 N²`; `kq q = (jq q · q + 1)/4` is attained, and the level of a prime is `0` exactly
below `kq`.  All λ-specific numerology (class `3 mod 4`: `k = (p+1)/4`; class `1 mod 4`:
`k = (3p+1)/4`) lives here and in `LambdaHybridContent`.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

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

end CatalanFrames.Lambda
