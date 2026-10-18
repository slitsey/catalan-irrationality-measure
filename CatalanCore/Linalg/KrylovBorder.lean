module

public import CatalanCore.Linalg.Krylov

/-!
# Bordering lemma (L5)

For `C : (m+1) × m`, `u(C Cᵀ, v) = det[v | C] · u(Cᵀ C, Cᵀ v)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {m : ℕ}

/-- The bordered matrix `[v | C]`. -/
def border (C : Matrix (Fin (m + 1)) (Fin m) F) (v : Fin (m + 1) → F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => Fin.cases (v i) (fun j' => C i j') j

lemma pow_mul_transpose (C : Matrix (Fin (m + 1)) (Fin m) F) (k : ℕ) :
    (C * Cᵀ) ^ (k + 1) = C * (Cᵀ * C) ^ k * Cᵀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- Block diagonal `1 ⊕ K'`. -/
def diagOne (K' : Matrix (Fin m) (Fin m) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun j k => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun k' => Fin.cases 0 (fun j' => K' j' k') j) k

lemma det_diagOne (K' : Matrix (Fin m) (Fin m) F) : (diagOne K').det = K'.det := by
  rw [Matrix.det_succ_column_zero]
  simp [diagOne, Fin.sum_univ_succ]
  congr 1

/-- **L5.** -/
theorem kdet_mul_transpose (C : Matrix (Fin (m + 1)) (Fin m) F) (v : Fin (m + 1) → F) :
    kdet (C * Cᵀ) v = (border C v).det * kdet (Cᵀ * C) (Cᵀ *ᵥ v) := by
  have h : krylov (C * Cᵀ) v = border C v * diagOne (krylov (Cᵀ * C) (Cᵀ *ᵥ v)) := by
    ext i k
    refine Fin.cases ?_ (fun k' => ?_) k
    · simp [border, diagOne, krylov_apply, Matrix.mul_apply, Fin.sum_univ_succ]
    · rw [krylov_apply, Fin.val_succ, pow_mul_transpose, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      simp [border, diagOne, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct,
        krylov_apply]
  rw [kdet, kdet, h, Matrix.det_mul, det_diagOne]

end CatalanCore
