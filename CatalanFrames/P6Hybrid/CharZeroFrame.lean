module

public import CatalanFrames.P6Hybrid.CharZeroAntidifference
public import CatalanFrames.P6.Frame
public import CatalanCore.Rect.CharZeroNV.After
public import CatalanCore.Rect.Full
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # The characteristic-zero interpolation data of the frozen P6 frame

This adapter uses the original rational prefixes and sign convention. It does
not change `Frame`, `Mn`, or any historical interface.
-/

open Polynomial Finset CatalanCore.Rect.CharZeroNV CatalanFrames.P6

namespace CatalanFrames.P6Hybrid.CharZeroNV

lemma increment_value (i : ℕ) :
    (incrementDen : ℚ[X]).eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) = 1 - (i : ℚ) := by
  rw [Delta_eq (i + 1) (by omega)]
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℚ) + 1 ≠ 0 := by linarith
  have h3 : 3 * (i : ℚ) + 1 ≠ 0 := by linarith
  have h2 : 2 * (i : ℚ) + 1 ≠ 0 := by linarith
  simp only [incrementDen, eval_mul, eval_ofNat, eval_add, eval_X, eval_one, eval_C, Nat.cast_succ]
  simp only [show 3 * ((i : ℚ) + 1) - 2 = 3 * (i : ℚ) + 1 by ring,
    show 2 * ((i : ℚ) + 1) - 1 = 2 * (i : ℚ) + 1 by ring]
  field_simp [h1, h2, h3]
  <;> ring

lemma increment_jet (i : ℕ) :
    (incrementDen : ℚ[X]).derivative.eval (i : ℚ) * (p6Frame.Delta (i + 1) / 36) -
      incrementDen.eval (i : ℚ) * (p6Frame.Dsq (i + 1) / 36) = -1 := by
  rw [Delta_eq (i + 1) (by omega), Dsq_eq (i + 1) (by omega)]
  have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
  have h1 : (i : ℚ) + 1 ≠ 0 := by linarith
  have h3 : 3 * (i : ℚ) + 1 ≠ 0 := by linarith
  have h2 : 2 * (i : ℚ) + 1 ≠ 0 := by linarith
  simp only [incrementDen, derivative_mul, derivative_add, derivative_X, derivative_one,
    derivative_C, derivative_ofNat, eval_add, eval_mul, eval_ofNat, eval_X, eval_one,
    eval_C, eval_zero, Nat.cast_succ]
  simp only [show 3 * ((i : ℚ) + 1) - 2 = 3 * (i : ℚ) + 1 by ring,
    show 2 * ((i : ℚ) + 1) - 1 = 2 * (i : ℚ) + 1 by ring]
  field_simp [h1, h2, h3]
  <;> ring

noncomputable def frameData (U : ℚ) : IncrementData (incrementDen : ℚ[X]) (1 - X) where
  f i := (∑ k ∈ Icc 1 i, p6Frame.Delta k) / 36
  tau i := U - (∑ k ∈ Icc 1 i, p6Frame.Dsq k) / 36
  value_step i := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
    simp only [add_div, add_sub_cancel_left, eval_sub, eval_one, eval_X]
    exact increment_value i
  jet_step i := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
    simp only [add_div, add_sub_cancel_left, derivative_sub, derivative_one,
      derivative_X, eval_sub, eval_zero, eval_one]
    linear_combination increment_jet i

lemma prefix_sub (g : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Icc 1 b, g k) - (∑ k ∈ Icc 1 a, g k) = ∑ k ∈ Ioc a b, g k := by
  have hs : Icc 1 a ⊆ Icc 1 b := by intro k hk; simp only [mem_Icc] at *; omega
  have he : Icc 1 b \ Icc 1 a = Ioc a b := by
    ext k
    simp only [mem_sdiff, mem_Icc, mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hs (f := g)
  rw [he] at hsum
  linear_combination -hsum

/-- Extend a natural-node datum to the ambient field; only its natural-node
values enter any of the interpolation and matrix statements. -/
noncomputable def onNaturals (g : ℕ → ℚ) : ℚ → ℚ :=
  Function.extend (Nat.cast : ℕ → ℚ) g (fun _ => 0)

@[simp] lemma onNaturals_nat (g : ℕ → ℚ) (i : ℕ) : onNaturals g (i : ℚ) = g i :=
  Nat.cast_injective.extend_apply g _ i

lemma mn_offdiag (U : ℚ) (a b : ℕ) (hab : a ≠ b) :
    p6Frame.Mn a b = ((frameData U).f a - (frameData U).f b) / ((a : ℚ) - b) := by
  unfold CatalanCore.Frame.Mn
  rw [if_neg hab]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
    have hs := prefix_sub p6Frame.Delta (Nat.le_of_lt h)
    dsimp [frameData]
    rw [← hs]
    norm_num only [p6Frame]
    rw [show (a : ℚ) - b = -((b : ℚ) - a) by ring, div_neg]
    simp only [div_eq_mul_inv]
    ring
  · rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
    have hs := prefix_sub p6Frame.Delta (Nat.le_of_lt h)
    dsimp [frameData]
    rw [← hs]
    norm_num only [p6Frame]
    ring

lemma loewnerEntry_nat (U : ℚ) (a b : ℕ) :
    loewnerEntry (onNaturals (frameData U).f) (onNaturals (frameData U).tau)
      (a : ℚ) (b : ℚ) = (if a = b then U else 0) + p6Frame.Mn a b := by
  by_cases hab : a = b
  · subst b
    simp [loewnerEntry, frameData, CatalanCore.Frame.Mn, p6Frame]
    ring
  · have hcast : (a : ℚ) ≠ b := by exact_mod_cast hab
    simp only [loewnerEntry, if_neg hcast, onNaturals_nat, if_neg hab, zero_add]
    exact (mn_offdiag U a b hab).symm

/-- The abstract matrix is precisely the frozen hybrid matrix after reindexing. -/
theorem fullN_eq_loewner (U : ℚ) (r m : ℕ) :
    CatalanCore.Rect.FullN p6Frame (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (loewnerMatrix (after r m) (onNaturals (frameData U).f)
        (onNaturals (frameData U).tau)).submatrix (afterRowEquiv r m) (afterRowEquiv r m) := by
  ext i j
  simp only [Matrix.submatrix_apply, loewnerMatrix, after_equiv_row,
    afterRowEquiv_val, afterColEquiv_val]
  rw [loewnerEntry_nat]
  rcases i with i | i <;> rcases j with j | j
  · simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkA,
      afterNodeNat, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> ring
  · have h : i.val ≠ r + 2 * j.val + 1 := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkB,
      afterNodeNat, h]
  · have h : r + 2 * i.val ≠ j.val := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkC,
      afterNodeNat, h]
  · have h : r + 2 * i.val ≠ r + 2 * j.val + 1 := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkD,
      afterNodeNat, h]

end CatalanFrames.P6Hybrid.CharZeroNV
