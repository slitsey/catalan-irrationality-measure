module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import CatalanCore.Basic.ZModGood
public import Mathlib.Tactic

@[expose] public section

/-! # Asymmetric exponent-one reduction for hybrid determinants

The finite block argument is independent of the frame and of the common-node
geometry. No inverse of the border kernel occurs.
-/

open Matrix

namespace CatalanCore.Arith.Hybrid.ValOne

variable {F : Type*} [Field F]
variable {L H B : Type*} [Fintype L] [DecidableEq L]
  [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]

/-- The three-block limit, in low/common-high/border order. -/
def limit (u d t : F) (WX WY : Matrix L B F) (A : Matrix H L F) :
    Matrix ((L ⊕ H) ⊕ B) ((L ⊕ H) ⊕ B) F
  | .inl (.inl i), .inl (.inl j) => u * (1 : Matrix L L F) i j
  | .inl (.inl _), .inl (.inr _) => 0
  | .inl (.inl i), .inr j => -t * WY i j
  | .inl (.inr i), .inl (.inl j) => A i j
  | .inl (.inr i), .inl (.inr j) => -d * (1 : Matrix H H F) i j
  | .inl (.inr _), .inr _ => 0
  | .inr i, .inl (.inl j) => -t * WX j i
  | .inr _, .inl (.inr _) => 0
  | .inr _, .inr _ => 0

private def swap : ((L ⊕ H) ⊕ B) ≃ ((L ⊕ B) ⊕ H) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr i
    | .inr i => .inl (.inr i)
  left_inv := by intro i; rcases i with (i | i) | i <;> rfl
  right_inv := by intro i; rcases i with (i | i) | i <;> rfl

/-- The low/border block is nonsingular from its cross Gram matrix. -/
theorem det_border_ne_zero (u t : F) (WX WY : Matrix L B F)
    (hu : u ≠ 0) (ht : t ≠ 0) (hG : (WX.transpose * WY).det ≠ 0) :
    (Matrix.fromBlocks (u • (1 : Matrix L L F)) (-t • WY)
      (-t • WX.transpose) (0 : Matrix B B F)).det ≠ 0 := by
  have hU : IsUnit (u • (1 : Matrix L L F)).det := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hu)
  letI : Invertible (u • (1 : Matrix L L F)) :=
    ⟨u⁻¹ • 1, by simp [smul_smul, hu], by simp [smul_smul, hu]⟩
  rw [Matrix.det_fromBlocks₁₁]
  have hi : ⅟(u • (1 : Matrix L L F)) = u⁻¹ • 1 :=
    invOf_eq_right_inv (by simp [smul_smul, hu])
  rw [hi]
  have hS : (0 : Matrix B B F) - (-t • WX.transpose) * (u⁻¹ • (1 : Matrix L L F)) *
      (-t • WY) = (-(t * u⁻¹ * t)) • (WX.transpose * WY) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, zero_sub]
    rw [← neg_smul]
    congr 1
    ring
  rw [hS]
  simp only [Matrix.det_smul, Matrix.det_one, mul_one]
  exact mul_ne_zero (pow_ne_zero _ hu)
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero ht (inv_ne_zero hu)) ht))) hG)

/-- Nonzero determinant of the asymmetric limit, with arbitrary high/low block. -/
theorem det_limit_ne_zero (u d t : F) (WX WY : Matrix L B F) (A : Matrix H L F)
    (hu : u ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0)
    (hG : (WX.transpose * WY).det ≠ 0) : (limit u d t WX WY A).det ≠ 0 := by
  let Q := Matrix.fromBlocks (u • (1 : Matrix L L F)) (-t • WY)
    (-t • WX.transpose) (0 : Matrix B B F)
  let C : Matrix H (L ⊕ B) F := fun i j => Sum.elim (A i) (fun _ => 0) j
  have he : Matrix.reindex (swap (L := L) (H := H) (B := B))
      (swap (L := L) (H := H) (B := B)) (limit u d t WX WY A) =
      Matrix.fromBlocks Q 0 C (-d • (1 : Matrix H H F)) := by
    ext i j
    rcases i with (i | i) | i <;> rcases j with (j | j) | j <;> rfl
  have hdet : (limit u d t WX WY A).det =
      Q.det * (-d • (1 : Matrix H H F)).det := by
    rw [← Matrix.det_reindex_self (swap (L := L) (H := H) (B := B)), he,
      Matrix.det_fromBlocks_zero₁₂]
  rw [hdet]
  exact mul_ne_zero (det_border_ne_zero u t WX WY hu ht hG)
    (by
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (neg_ne_zero.mpr hd))

end CatalanCore.Arith.Hybrid.ValOne


namespace CatalanCore.Arith.Hybrid.ValOne

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {L H B : Type*} [Fintype L] [DecidableEq L]
  [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]

/-- A determinant with a nonsingular asymmetric reduction is nonzero.
The row and column multipliers need not be units. -/
theorem det_ne_zero_of_good (M : Matrix ((L ⊕ H) ⊕ B) ((L ⊕ H) ⊕ B) ℚ)
    (row col : ((L ⊕ H) ⊕ B) → ℚ)
    (u d t : ZMod ℓ) (WX WY : Matrix L B (ZMod ℓ)) (A : Matrix H L (ZMod ℓ))
    (hu : u ≠ 0) (hd : d ≠ 0) (ht : t ≠ 0)
    (hG : (WX.transpose * WY).det ≠ 0)
    (hGood : ∀ i j, Good ℓ (row i * M i j * col j) (limit u d t WX WY A i j)) :
    M.det ≠ 0 := by
  let N : Matrix ((L ⊕ H) ⊕ B) ((L ⊕ H) ⊕ B) ℚ :=
    fun i j => row i * M i j * col j
  have hN : N = Matrix.diagonal row * M * Matrix.diagonal col := by
    ext i j
    simp [N, Matrix.diagonal_mul, Matrix.mul_diagonal]
  intro hM
  have h0 : N.det = 0 := by rw [hN, Matrix.det_mul, Matrix.det_mul, hM]; simp
  exact det_limit_ne_zero u d t WX WY A hu hd ht hG ((red_det N _ hGood).eq_zero h0)

end CatalanCore.Arith.Hybrid.ValOne
