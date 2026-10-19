module

public import CatalanCore.Arith.Hybrid.DefC7Entries

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4): the symmetric residue table `TcF7` and its basic values

`TcF7 p r k A B` is the reduction mod `p` of `p^{wC7 A + wC7 B} Mn A B` (D2 weights), for labels
`A, B < r + 2m` (`good_TcF7`, `good_TcD7`); the values used by the Schur complement are collected here.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Tab7

variable (p : ℕ) [Fact p.Prime] (r k : ℕ)

/-- The symmetric residue table on labels. -/
noncomputable def TcF7 (A B : ℕ) : ZMod p :=
  if A < B then TCgen7 p k (wC7 p r k A + wC7 p r k B) A B
  else if B < A then TCgen7 p k (wC7 p r k B + wC7 p r k A) B A
  else TCDgen7 p k (wC7 p r k A + wC7 p r k A) A

variable {p r k}

lemma TcF7_symm (A B : ℕ) : TcF7 p r k A B = TcF7 p r k B A := by
  unfold TcF7
  split_ifs <;> first | omega | rfl | (obtain rfl : A = B := by omega
                                       rfl)

lemma TcF7_lt {A B : ℕ} (h : A < B) :
    TcF7 p r k A B = TCgen7 p k (wC7 p r k A + wC7 p r k B) A B := by
  unfold TcF7; rw [if_pos h]

lemma TcF7_diag (A : ℕ) :
    TcF7 p r k A A = TCDgen7 p k (wC7 p r k A + wC7 p r k A) A := by
  unfold TcF7; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

section Wt7

variable {o m : ℕ} (S : CSetup7 o p r m k)
include S

lemma wC7_U {A : ℕ} (h1 : r - p ≤ A) (h2 : A < k) : wC7 p r k A = 0 := by
  have := S.kp; have := S.hrp; unfold wC7; split_ifs <;> omega

lemma wC7_P {A : ℕ} (hA : A < r) (h : ¬ (r - p ≤ A ∧ A < k)) : wC7 p r k A = 1 := by
  unfold wC7; split_ifs <;> omega

lemma wC7_low {A : ℕ} (h1 : r ≤ A) (h2 : A < p + k) : wC7 p r k A = 2 := by
  unfold wC7; split_ifs <;> omega

lemma wC7_high {A : ℕ} (h1 : p + k ≤ A) : wC7 p r k A = 1 := by
  have := S.hLlo; unfold wC7; split_ifs <;> omega

lemma wC7_le {A : ℕ} : wC7 p r k A ≤ 2 := by unfold wC7; split_ifs <;> omega

variable {Fr : Frame} (hL : LamData Fr o)
include hL

theorem good_TcF7 {A B : ℕ} (hAB : A ≠ B) (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (wC7 p r k A + wC7 p r k B) * Fr.Mn A B) (TcF7 p r k A B) := by
  have hkp := S.kp
  have hrp := S.hrp
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hN := S.hN
  rcases lt_or_gt_of_ne hAB with h | h
  · rw [TcF7_lt h]
    refine good_TCgen7 hL S h hB ?_ ?_
    · intro hw; unfold wC7 at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC7 at hw; split_ifs at hw <;> omega
  · rw [TcF7_symm, TcF7_lt h, Mn_symm, add_comm]
    refine good_TCgen7 hL S h hA ?_ ?_
    · intro hw; unfold wC7 at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC7 at hw; split_ifs at hw <;> omega

theorem good_TcD7 {A : ℕ} (hA : A < r) :
    Good p ((p : ℚ) ^ (wC7 p r k A + wC7 p r k A) * Fr.Mn A A) (TcF7 p r k A A) := by
  have hkp := S.kp
  have hrp := S.hrp
  rw [TcF7_diag]
  refine good_TCDgen7 hL S hA ?_ ?_
  · unfold wC7; split_ifs <;> omega
  · intro hw; unfold wC7 at hw; split_ifs at hw <;> omega

end Wt7

end Tab7

end CatalanCore.Arith.Hybrid
