module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3B

@[expose] public section

/-!
# Lemma E, class 3: evaluation of the table `TEw3` on the label classes
-/

open Finset

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

lemma TEoG_big {N : ℕ} (D : SingData p N k1) {w : ℕ} (hw : 3 ≤ w) (A B : ℕ) : TEoG D w A B = 0 := by
  unfold TEoG
  by_cases h : B - A = p
  · simp [h, show w ≠ 2 by omega]
  · simp [h, show w ≠ 1 by omega]

lemma TEoG_two {N : ℕ} (D : SingData p N k1) (A B : ℕ) : TEoG D 2 A B =
    if B - A = p then (16 : ZMod p)⁻¹ * singG D A B else 0 := by
  unfold TEoG
  by_cases h : B - A = p <;> simp [h]

lemma TEoG_one {N : ℕ} (D : SingData p N k1) {A B : ℕ} (h : B - A ≠ p) :
    TEoG D 1 A B = (16 * ((B : ZMod p) - A))⁻¹ * singG D A B := by
  unfold TEoG; simp [h]

lemma TEdG_two {N : ℕ} (D : SingData p N k1) (A : ℕ) :
    TEdG D 2 A = -(1 / 16 : ZMod p) * singG2 D A := by
  unfold TEdG; simp

lemma TEw3_lt (D : SingData p (r + 2 * m) k1) {A B : ℕ} (h : A < B) :
    TEw3 p r m D A B = TEoG D (wr p r m A + wc p r m B) A B := by
  unfold TEw3; rw [if_pos h]

lemma TEw3_gt (D : SingData p (r + 2 * m) k1) {A B : ℕ} (h : B < A) :
    TEw3 p r m D A B = TEoG D (wr p r m A + wc p r m B) B A := by
  unfold TEw3; rw [if_neg (by omega), if_pos h]

lemma TEw3_eq (D : SingData p (r + 2 * m) k1) (A : ℕ) :
    TEw3 p r m D A A = TEdG D (wr p r m A + wc p r m A) A := by
  unfold TEw3; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

variable (S : ESetup3 o p r m k1)

lemma singG_eval (A B : ℕ) : singG (sd3 S) A B =
    (if A < k1 ∧ k1 ≤ B then -(4 * (((1 : ℕ) : ZMod p))⁻¹) else 0) +
    (if A < p ∧ p ≤ B then 1 else 0) +
    (if A < p + k1 ∧ p + k1 ≤ B then -(4 * (((5 : ℕ) : ZMod p))⁻¹) else 0) := by
  have hk1 := S.hk1o
  have hp5 := S.p5
  have h1 : k1 ≠ p := by omega
  have h2 : k1 ≠ p + k1 := by omega
  have h3 : p ≠ p + k1 := by omega
  have hp0 : p ≠ 0 := by omega
  have hk0 : k1 ≠ 0 := by omega
  unfold singG
  simp only [sd3]
  rw [Finset.sum_filter]
  rw [Finset.sum_insert (by simp [h1, hp0, hk0]), Finset.sum_insert (by simp [hk0]), Finset.sum_singleton]
  simp [h1, h2, h3, h1.symm, h2.symm, h3.symm, hp0, hk0]
  try ring

lemma singG2_eval (A : ℕ) : singG2 (sd3 S) A =
    (if k1 ≤ A then -(16 * ((((1 : ℕ) : ZMod p))⁻¹) ^ 2) else 0) +
    (if p ≤ A then 1 else 0) +
    (if p + k1 ≤ A then -(16 * ((((5 : ℕ) : ZMod p))⁻¹) ^ 2) else 0) := by
  have hk1 := S.hk1o
  have hp5 := S.p5
  have h1 : k1 ≠ p := by omega
  have h2 : k1 ≠ p + k1 := by omega
  have h3 : p ≠ p + k1 := by omega
  have hp0 : p ≠ 0 := by omega
  have hk0 : k1 ≠ 0 := by omega
  unfold singG2
  simp only [sd3]
  rw [Finset.sum_filter]
  rw [Finset.sum_insert (by simp [h1, hp0, hk0]), Finset.sum_insert (by simp [hk0]), Finset.sum_singleton]
  simp [h1, h2, h3, h1.symm, h2.symm, h3.symm, hp0, hk0]
  try ring

end

end CatalanCore.Arith.Hybrid
