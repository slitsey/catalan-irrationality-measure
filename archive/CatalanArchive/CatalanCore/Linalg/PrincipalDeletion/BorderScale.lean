module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic
@[expose] public section
open Matrix
namespace CatalanCore.Linalg.PrincipalDeletion
variable {F : Type*} [Field F] {A B : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
/-- Scaling only the low block by a unit preserves nonsingularity of a bordered matrix. -/
theorem bordered_smul_ne_zero (M : Matrix A A F) (X Y : Matrix A B F)
    (c : F) (hc : c ≠ 0)
    (hdet : (fromBlocks M Y X.transpose (0 : Matrix B B F)).det ≠ 0) :
    (fromBlocks (c • M) Y X.transpose (0 : Matrix B B F)).det ≠ 0 := by
  let L : Matrix (A ⊕ B) (A ⊕ B) F := fromBlocks (c • 1) 0 0 1
  let R : Matrix (A ⊕ B) (A ⊕ B) F := fromBlocks 1 0 0 (c⁻¹ • 1)
  have he : fromBlocks (c • M) Y X.transpose (0 : Matrix B B F) =
      L * fromBlocks M Y X.transpose 0 * R := by
    simp only [L, R, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, smul_zero, smul_smul]
    ext (a | b) (i | j) <;> simp [hc]
  rw [he, Matrix.det_mul, Matrix.det_mul]
  apply mul_ne_zero (mul_ne_zero ?_ hdet) ?_
  · simp [L, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, hc]
  · simp [R, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, hc]
end CatalanCore.Linalg.PrincipalDeletion
#print axioms CatalanCore.Linalg.PrincipalDeletion.bordered_smul_ne_zero
