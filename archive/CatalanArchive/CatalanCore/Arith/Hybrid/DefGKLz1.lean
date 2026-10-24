module

public import CatalanArchive.CatalanCore.Arith.Hybrid.DefGKInst1
public import CatalanArchive.CatalanCore.Arith.Hybrid.DefGKLz3

@[expose] public section

/-!
# GK, class 1: integer-scaled cumulative residues

`Lz1 n = 84 · Lv n`, `Pz1 n = 1764 · Pv n` and `Qz1 A B = 56448 · Q(A,B)`:

* `Qz1 A B = 42 (Lz1 B - Lz1 A)` for `B - A = p`, `21 (Lz1 B - Lz1 A)` for `B - A = 2p`,
  `0` for other `A < B`, and `-2 Pz1 A` on the diagonal.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Lz1

variable {o p : ℕ} [Fact p.Prime]

/-- `84 · Lv`. -/
def Lz1 (p k n : ℕ) : ℤ :=
  (if k ≤ n then -112 else 0) + (if p ≤ n then 84 else 0) + (if p + k ≤ n then -48 else 0) +
    (if 2 * p ≤ n then 42 else 0)

/-- `1764 · Pv`. -/
def Pz1 (p k n : ℕ) : ℤ :=
  (if k ≤ n then -3136 else 0) + (if p ≤ n then 1764 else 0) +
    (if p + k ≤ n then -576 else 0) + (if 2 * p ≤ n then 441 else 0)

section Blocks

variable {k : ℕ} (h13 : 13 ≤ p) (hk : 4 * k = 3 * p + o ∧ 0 < o ∧ o ≤ 3) {n : ℕ}
include h13 hk

lemma Lz_B0 (h : n < k) : Lz1 p k n = 0 := by unfold Lz1; split_ifs <;> omega
lemma Lz_B1 (h1 : k ≤ n) (h2 : n < p) : Lz1 p k n = -112 := by unfold Lz1; split_ifs <;> omega
lemma Lz_B2 (h1 : p ≤ n) (h2 : n < p + k) : Lz1 p k n = -28 := by unfold Lz1; split_ifs <;> omega
lemma Lz_B3 (h1 : p + k ≤ n) (h2 : n < 2 * p) : Lz1 p k n = -76 := by
  unfold Lz1; split_ifs <;> omega
lemma Lz_B4 (h1 : 2 * p ≤ n) : Lz1 p k n = -34 := by unfold Lz1; split_ifs <;> omega

lemma Pz_B0 (h : n < k) : Pz1 p k n = 0 := by unfold Pz1; split_ifs <;> omega
lemma Pz_B1 (h1 : k ≤ n) (h2 : n < p) : Pz1 p k n = -3136 := by unfold Pz1; split_ifs <;> omega
lemma Pz_B2 (h1 : p ≤ n) (h2 : n < p + k) : Pz1 p k n = -1372 := by
  unfold Pz1; split_ifs <;> omega
lemma Pz_B3 (h1 : p + k ≤ n) (h2 : n < 2 * p) : Pz1 p k n = -1948 := by
  unfold Pz1; split_ifs <;> omega
lemma Pz_B4 (h1 : 2 * p ≤ n) : Pz1 p k n = -1507 := by unfold Pz1; split_ifs <;> omega

end Blocks

/-- `56448 · (the p²-level residue table of Mn)`, integer valued. -/
def Qz1 (p k A B : ℕ) : ℤ :=
  if A < B then
    (if B - A = p then 42 * (Lz1 p k B - Lz1 p k A)
     else if B - A = 2 * p then 21 * (Lz1 p k B - Lz1 p k A) else 0)
  else if B < A then
    (if A - B = p then 42 * (Lz1 p k A - Lz1 p k B)
     else if A - B = 2 * p then 21 * (Lz1 p k A - Lz1 p k B) else 0)
  else -2 * Pz1 p k A

lemma Qz1_symm (p k A B : ℕ) : Qz1 p k A B = Qz1 p k B A := by
  unfold Qz1
  split_ifs <;> first | rfl | (exfalso; omega) | (have hAB : A = B := (by omega); subst hAB; rfl)

lemma Qz1_diag (p k A : ℕ) : Qz1 p k A A = -2 * Pz1 p k A := by
  unfold Qz1; simp

lemma Qz1_p (p k A : ℕ) (hp : 0 < p) : Qz1 p k A (A + p) = 42 * (Lz1 p k (A + p) - Lz1 p k A) := by
  unfold Qz1; rw [if_pos (by omega), if_pos (by omega)]

lemma Qz1_2p (p k A : ℕ) (hp : 0 < p) :
    Qz1 p k A (A + 2 * p) = 21 * (Lz1 p k (A + 2 * p) - Lz1 p k A) := by
  unfold Qz1; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]

lemma Qz1_zero (p k A B : ℕ) (h1 : A ≠ B) (h2 : A + p ≠ B) (h3 : B + p ≠ A) (h4 : A + 2 * p ≠ B)
    (h5 : B + 2 * p ≠ A) : Qz1 p k A B = 0 := by
  unfold Qz1
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Nonvanishing of the scaling constants -/

lemma ne_zero_smooth7 (h13 : 13 ≤ p) (a b c : ℕ) : ((2 ^ a * 3 ^ b * 7 ^ c : ℕ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

lemma n7 (h13 : 13 ≤ p) : (7 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 0 0 1
  norm_num at this; exact this

lemma n49 (h13 : 13 ≤ p) : (49 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 0 0 2
  norm_num at this; exact this

lemma n84 (h13 : 13 ≤ p) : (84 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 2 1 1
  norm_num at this; exact this

lemma n1764 (h13 : 13 ≤ p) : (1764 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 2 2 2
  norm_num at this; exact this

lemma n56448 (h13 : 13 ≤ p) : (56448 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 7 2 2
  norm_num at this; exact this

lemma n28 (h13 : 13 ≤ p) : (28 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth7 (p := p) h13 2 0 1
  norm_num at this; exact this

/-! ### Relation to the cumulative residues -/

variable {k : ℕ}

lemma Lv_Sg1 {r m : ℕ} (S : GKS1 o p r m k) (n : ℕ) :
    Lv (Sg1 p k) (res1 p k) n =
      (if k ≤ n then res1 p k k else 0) + (if p ≤ n then res1 p k p else 0) +
        (if p + k ≤ n then res1 p k (p + k) else 0) + (if 2 * p ≤ n then res1 p k (2 * p) else 0) := by
  have := S.kp; have := S.k0; have := S.p13
  unfold Lv Sg1
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  ring

lemma Pv_Sg1 {r m : ℕ} (S : GKS1 o p r m k) (n : ℕ) :
    Lv (Sg1 p k) (resD1 p k) n =
      (if k ≤ n then resD1 p k k else 0) + (if p ≤ n then resD1 p k p else 0) +
        (if p + k ≤ n then resD1 p k (p + k) else 0) +
        (if 2 * p ≤ n then resD1 p k (2 * p) else 0) := by
  have := S.kp; have := S.k0; have := S.p13
  unfold Lv Sg1
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  ring

lemma Lv_eq_Lz {r m : ℕ} (S : GKS1 o p r m k) (n : ℕ) :
    Lv (Sg1 p k) (res1 p k) n = (Lz1 p k n : ZMod p) * 84⁻¹ := by
  have h13 := S.p13
  have hkp := S.kp; have hk0 := S.k0
  have n84' := n84 (p := p) h13
  have n3' := n3 (p := p) h13
  have n7' := n7 (p := p) h13
  have n2' := n2 (p := p) h13
  have e1 : k ≠ p := by omega
  have e2 : k ≠ p + k := by omega
  have e3 : p ≠ p + k := by omega
  have e4 : k ≠ 2 * p := by omega
  have e5 : p ≠ 2 * p := by omega
  have e6 : p + k ≠ 2 * p := by omega
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  rw [Lv_Sg1 S]
  unfold Lz1
  have r1 : res1 p k k = ((-112 : ℤ) : ZMod p) * 84⁻¹ := by
    simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  have r2 : res1 p k p = ((84 : ℤ) : ZMod p) * 84⁻¹ := by
    simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp
  have r3 : res1 p k (p + k) = ((-48 : ℤ) : ZMod p) * 84⁻¹ := by
    simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  have r4 : res1 p k (2 * p) = ((42 : ℤ) : ZMod p) * 84⁻¹ := by
    simp [res1, np, nk, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      e6.symm]
    field_simp; norm_num
  rw [ite_cast_mul _ _ _ _ r1, ite_cast_mul _ _ _ _ r2, ite_cast_mul _ _ _ _ r3,
    ite_cast_mul _ _ _ _ r4]
  push_cast
  ring

end Lz1

end CatalanCore.Arith.Hybrid.GK1
