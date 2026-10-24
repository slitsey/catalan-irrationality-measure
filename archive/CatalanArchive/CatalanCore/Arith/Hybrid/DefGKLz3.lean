module

public import CatalanArchive.CatalanCore.Arith.Hybrid.DefGKInst3

@[expose] public section

/-!
# GK, class 3: integer-scaled cumulative residues

`Lz3 n = 90 · Lv n`, `Pz3 n = 8100 · Pv n` are integers (`Lv`, `Pv` are the cumulative residues of
`p Δ_t`, `p² D_t` over `{k, p, p+k, 2p, 2p+k}`), and `Qz3 A B = 129600 · Q(A,B)` where
`Q` is the `p²`-level residue table of `Mn`:

* `Qz3 A B = 90 (Lz3 B - Lz3 A)` for `B - A = p`,  `45 (Lz3 B - Lz3 A)` for `B - A = 2p`,
  `0` for other `A < B`, and `-Pz3 A` on the diagonal.

`good_Qz3`: `Good p (p² Mn A B) (Qz3 A B / 129600)` for all labels `A, B < r + 2m` (diagonal for `A < r`).
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Lz3

variable {o p : ℕ} [Fact p.Prime]

/-- `90 · Lv`. -/
def Lz3 (p k n : ℕ) : ℤ :=
  (if k ≤ n then -360 else 0) + (if p ≤ n then 90 else 0) + (if p + k ≤ n then -72 else 0) +
    (if 2 * p ≤ n then 45 else 0) + (if 2 * p + k ≤ n then -40 else 0)

/-- `8100 · Pv`. -/
def Pz3 (p k n : ℕ) : ℤ :=
  (if k ≤ n then -129600 else 0) + (if p ≤ n then 8100 else 0) +
    (if p + k ≤ n then -5184 else 0) + (if 2 * p ≤ n then 2025 else 0) +
    (if 2 * p + k ≤ n then -1600 else 0)

section Blocks

variable {k : ℕ} (h13 : 13 ≤ p) (hk : 4 * k = p + o ∧ 0 < o ∧ o ≤ 3) {n : ℕ}
include h13 hk

lemma Lz_B0 (h : n < k) : Lz3 p k n = 0 := by unfold Lz3; split_ifs <;> omega
lemma Lz_B1 (h1 : k ≤ n) (h2 : n < p) : Lz3 p k n = -360 := by unfold Lz3; split_ifs <;> omega
lemma Lz_B2 (h1 : p ≤ n) (h2 : n < p + k) : Lz3 p k n = -270 := by unfold Lz3; split_ifs <;> omega
lemma Lz_B3 (h1 : p + k ≤ n) (h2 : n < 2 * p) : Lz3 p k n = -342 := by unfold Lz3; split_ifs <;> omega
lemma Lz_B4 (h1 : 2 * p ≤ n) (h2 : n < 2 * p + k) : Lz3 p k n = -297 := by
  unfold Lz3; split_ifs <;> omega
lemma Lz_B5 (h1 : 2 * p + k ≤ n) : Lz3 p k n = -337 := by unfold Lz3; split_ifs <;> omega

lemma Pz_B0 (h : n < k) : Pz3 p k n = 0 := by unfold Pz3; split_ifs <;> omega
lemma Pz_B1 (h1 : k ≤ n) (h2 : n < p) : Pz3 p k n = -129600 := by unfold Pz3; split_ifs <;> omega
lemma Pz_B2 (h1 : p ≤ n) (h2 : n < p + k) : Pz3 p k n = -121500 := by
  unfold Pz3; split_ifs <;> omega
lemma Pz_B3 (h1 : p + k ≤ n) (h2 : n < 2 * p) : Pz3 p k n = -126684 := by
  unfold Pz3; split_ifs <;> omega
lemma Pz_B4 (h1 : 2 * p ≤ n) (h2 : n < 2 * p + k) : Pz3 p k n = -124659 := by
  unfold Pz3; split_ifs <;> omega
lemma Pz_B5 (h1 : 2 * p + k ≤ n) : Pz3 p k n = -126259 := by unfold Pz3; split_ifs <;> omega

end Blocks

/-- `129600 · (the p²-level residue table of Mn)`, integer valued. -/
def Qz3 (p k A B : ℕ) : ℤ :=
  if A < B then
    (if B - A = p then 90 * (Lz3 p k B - Lz3 p k A)
     else if B - A = 2 * p then 45 * (Lz3 p k B - Lz3 p k A) else 0)
  else if B < A then
    (if A - B = p then 90 * (Lz3 p k A - Lz3 p k B)
     else if A - B = 2 * p then 45 * (Lz3 p k A - Lz3 p k B) else 0)
  else -Pz3 p k A

lemma Qz3_symm (p k A B : ℕ) : Qz3 p k A B = Qz3 p k B A := by
  unfold Qz3
  split_ifs <;> first | rfl | (exfalso; omega) | (have hAB : A = B := (by omega); subst hAB; rfl)

lemma Qz3_diag (p k A : ℕ) : Qz3 p k A A = -Pz3 p k A := by
  unfold Qz3; simp

lemma Qz3_p (p k A : ℕ) (hp : 0 < p) : Qz3 p k A (A + p) = 90 * (Lz3 p k (A + p) - Lz3 p k A) := by
  unfold Qz3; rw [if_pos (by omega), if_pos (by omega)]

lemma Qz3_2p (p k A : ℕ) (hp : 0 < p) :
    Qz3 p k A (A + 2 * p) = 45 * (Lz3 p k (A + 2 * p) - Lz3 p k A) := by
  unfold Qz3; rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]

lemma Qz3_zero (p k A B : ℕ) (h1 : A ≠ B) (h2 : A + p ≠ B) (h3 : B + p ≠ A) (h4 : A + 2 * p ≠ B)
    (h5 : B + 2 * p ≠ A) : Qz3 p k A B = 0 := by
  unfold Qz3
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Relation to the cumulative residues -/

lemma ne_zero_smooth (h13 : 13 ≤ p) (a b c : ℕ) : ((2 ^ a * 3 ^ b * 5 ^ c : ℕ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

lemma n90 (h13 : 13 ≤ p) : (90 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 1 2 1
  norm_num at this; exact this

lemma n8100 (h13 : 13 ≤ p) : (8100 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 2 4 2
  norm_num at this; exact this

lemma n129600 (h13 : 13 ≤ p) : (129600 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 6 4 2
  norm_num at this; exact this

lemma n16 (h13 : 13 ≤ p) : (16 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 4 0 0
  norm_num at this; exact this

lemma n32 (h13 : 13 ≤ p) : (32 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 5 0 0
  norm_num at this; exact this

lemma n2 (h13 : 13 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 1 0 0
  norm_num at this; exact this

lemma n3 (h13 : 13 ≤ p) : (3 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 0 1 0
  norm_num at this; exact this

lemma n5 (h13 : 13 ≤ p) : (5 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 0 0 1
  norm_num at this; exact this

lemma n4 (h13 : 13 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 2 0 0
  norm_num at this; exact this

lemma n9 (h13 : 13 ≤ p) : (9 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 0 2 0
  norm_num at this; exact this

lemma n25 (h13 : 13 ≤ p) : (25 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 0 0 2
  norm_num at this; exact this

lemma n81 (h13 : 13 ≤ p) : (81 : ZMod p) ≠ 0 := by
  have := ne_zero_smooth (p := p) h13 0 4 0
  norm_num at this; exact this

lemma ite_cast_mul (c : Prop) [Decidable c] (x : ZMod p) (z : ℤ) (c0 : ZMod p)
    (h : x = (z : ZMod p) * c0) :
    (if c then x else 0) = ((if c then z else 0 : ℤ) : ZMod p) * c0 := by
  split_ifs <;> simp [h]

variable {k : ℕ}

lemma Lv_Sg3 {r m : ℕ} (S : GKS3 o p r m k) (n : ℕ) :
    Lv (Sg3 p k) (res3 p k) n =
      (if k ≤ n then res3 p k k else 0) + (if p ≤ n then res3 p k p else 0) +
        (if p + k ≤ n then res3 p k (p + k) else 0) + (if 2 * p ≤ n then res3 p k (2 * p) else 0) +
        (if 2 * p + k ≤ n then res3 p k (2 * p + k) else 0) := by
  have := S.kp; have := S.k0; have := S.p13
  unfold Lv Sg3
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  ring

lemma Pv_Sg3 {r m : ℕ} (S : GKS3 o p r m k) (n : ℕ) :
    Lv (Sg3 p k) (resD3 p k) n =
      (if k ≤ n then resD3 p k k else 0) + (if p ≤ n then resD3 p k p else 0) +
        (if p + k ≤ n then resD3 p k (p + k) else 0) + (if 2 * p ≤ n then resD3 p k (2 * p) else 0) +
        (if 2 * p + k ≤ n then resD3 p k (2 * p + k) else 0) := by
  have := S.kp; have := S.k0; have := S.p13
  unfold Lv Sg3
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  ring

lemma Lv_eq_Lz {r m : ℕ} (S : GKS3 o p r m k) (n : ℕ) :
    Lv (Sg3 p k) (res3 p k) n = (Lz3 p k n : ZMod p) * 90⁻¹ := by
  have h13 := S.p13
  have hkp := S.kp; have hk0 := S.k0
  have n90' := n90 (p := p) h13
  have n5' := n5 (p := p) h13
  have n9' := n9 (p := p) h13
  have n2' := n2 (p := p) h13
  have e1 : k ≠ p := by omega
  have e2 : k ≠ p + k := by omega
  have e3 : p ≠ p + k := by omega
  have e4 : k ≠ 2 * p := by omega
  have e5 : p ≠ 2 * p := by omega
  have e6 : p + k ≠ 2 * p := by omega
  have e7 : 2 * p + k ≠ k := by omega
  have e8 : 2 * p + k ≠ p := by omega
  have e9 : 2 * p + k ≠ p + k := by omega
  have e10 : 2 * p + k ≠ 2 * p := by omega
  have np : p ≠ 0 := by omega
  have nk : k ≠ 0 := by omega
  rw [Lv_Sg3 S]
  unfold Lz3
  have r1 : res3 p k k = ((-360 : ℤ) : ZMod p) * 90⁻¹ := by
    simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]; field_simp; norm_num
  have r2 : res3 p k p = ((90 : ℤ) : ZMod p) * 90⁻¹ := by
    simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]; field_simp
  have r3 : res3 p k (p + k) = ((-72 : ℤ) : ZMod p) * 90⁻¹ := by
    simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]; field_simp; norm_num
  have r4 : res3 p k (2 * p) = ((45 : ℤ) : ZMod p) * 90⁻¹ := by
    simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]; field_simp; norm_num
  have r5 : res3 p k (2 * p + k) = ((-40 : ℤ) : ZMod p) * 90⁻¹ := by
    simp [res3, np, nk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm]; field_simp; norm_num
  rw [ite_cast_mul _ _ _ _ r1, ite_cast_mul _ _ _ _ r2, ite_cast_mul _ _ _ _ r3,
    ite_cast_mul _ _ _ _ r4, ite_cast_mul _ _ _ _ r5]
  push_cast
  ring

end Lz3

end CatalanCore.Arith.Hybrid
