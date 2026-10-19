module

public import CatalanCore.Arith.Hybrid.DefC5Entries

@[expose] public section

/-!
# Theorem C5: the symmetric residue table `TcF` and its basic values

`TcF p r k A B` is the reduction mod `p` of `p^{wC A + wC B} Mn A B` (D2 weights), for labels
`A, B < r + 2m` (`good_TcF`, `good_TcD`); the values used by the Schur complement are collected here.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Tab

variable (p : ℕ) [Fact p.Prime] (r k : ℕ)

/-- The symmetric residue table on labels. -/
noncomputable def TcF (A B : ℕ) : ZMod p :=
  if A < B then TCgen p k (wC p r k A + wC p r k B) A B
  else if B < A then TCgen p k (wC p r k B + wC p r k A) B A
  else TCDgen p k (wC p r k A + wC p r k A) A

variable {p r k}

lemma TcF_symm (A B : ℕ) : TcF p r k A B = TcF p r k B A := by
  unfold TcF
  split_ifs <;> first | omega | rfl | (obtain rfl : A = B := by omega
                                       rfl)

lemma TcF_lt {A B : ℕ} (h : A < B) :
    TcF p r k A B = TCgen p k (wC p r k A + wC p r k B) A B := by
  unfold TcF; rw [if_pos h]

lemma TcF_diag (A : ℕ) :
    TcF p r k A A = TCDgen p k (wC p r k A + wC p r k A) A := by
  unfold TcF; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

section Wt

variable {m : ℕ} (S : CSetup p r m k)
include S

lemma wC_U {A : ℕ} (h1 : r - p ≤ A) (h2 : A < k) : wC p r k A = 0 := by
  have := S.kp; have := S.hrp; unfold wC; split_ifs <;> omega

lemma wC_P {A : ℕ} (hA : A < r) (h : ¬ (r - p ≤ A ∧ A < k)) : wC p r k A = 1 := by
  unfold wC; split_ifs <;> omega

lemma wC_low {A : ℕ} (h1 : r ≤ A) (h2 : A < p + k) : wC p r k A = 2 := by
  unfold wC; split_ifs <;> omega

lemma wC_high {A : ℕ} (h1 : p + k ≤ A) : wC p r k A = 1 := by
  have := S.hLlo; unfold wC; split_ifs <;> omega

lemma wC_le {A : ℕ} : wC p r k A ≤ 2 := by unfold wC; split_ifs <;> omega

variable {Fr : Frame} (hL : LamData Fr)
include hL

theorem good_TcF {A B : ℕ} (hAB : A ≠ B) (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (wC p r k A + wC p r k B) * Fr.Mn A B) (TcF p r k A B) := by
  have hkp := S.kp
  have hrp := S.hrp
  have hLlo := S.hLlo
  have hLhi := S.hLhi
  have hN := S.hN
  rcases lt_or_gt_of_ne hAB with h | h
  · rw [TcF_lt h]
    refine good_TCgen hL S h hB ?_ ?_
    · intro hw; unfold wC at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC at hw; split_ifs at hw <;> omega
  · rw [TcF_symm, TcF_lt h, Mn_symm, add_comm]
    refine good_TCgen hL S h hA ?_ ?_
    · intro hw; unfold wC at hw; split_ifs at hw <;> omega
    · intro hw hd; unfold wC at hw; split_ifs at hw <;> omega

theorem good_TcD {A : ℕ} (hA : A < r) :
    Good p ((p : ℚ) ^ (wC p r k A + wC p r k A) * Fr.Mn A A) (TcF p r k A A) := by
  have hkp := S.kp
  have hrp := S.hrp
  rw [TcF_diag]
  refine good_TCDgen hL S hA ?_ ?_
  · unfold wC; split_ifs <;> omega
  · intro hw; unfold wC at hw; split_ifs at hw <;> omega

end Wt

end Tab

end CatalanCore.Arith.Hybrid
