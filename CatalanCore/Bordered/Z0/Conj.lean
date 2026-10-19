module

public import CatalanCore.Linalg.Krylov
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Z0.1-Z0.3, Z0.5: Krylov determinants under conjugation, diagonal matrices, cross-ratio
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

open CatalanCore

variable {R : Type*} [CommRing R] {n : ℕ}

lemma pow_conj (M P : Matrix (Fin n) (Fin n) R) (hP : IsUnit P.det) (k : ℕ) :
    (P⁻¹ * M * P) ^ k = P⁻¹ * M ^ k * P := by
  induction k with
  | zero => simp [Matrix.nonsing_inv_mul _ hP]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc P⁻¹ * M ^ k * P * (P⁻¹ * M * P)
        = P⁻¹ * M ^ k * (P * P⁻¹) * M * P := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (M ^ k * M) * P := by rw [Matrix.mul_nonsing_inv _ hP]; simp [Matrix.mul_assoc]

/-- **Z0.1.** -/
theorem kdet_conj (M P : Matrix (Fin n) (Fin n) R) (hP : IsUnit P.det) (v : Fin n → R) :
    kdet (P⁻¹ * M * P) (P⁻¹ *ᵥ v) * P.det = kdet M v := by
  have hk : krylov (P⁻¹ * M * P) (P⁻¹ *ᵥ v) = P⁻¹ * krylov M v := by
    refine Matrix.ext fun i k => ?_
    have e : (P⁻¹ * M ^ (k : ℕ) * P) *ᵥ (P⁻¹ *ᵥ v) = P⁻¹ *ᵥ (M ^ (k : ℕ) *ᵥ v) := by
      calc (P⁻¹ * M ^ (k : ℕ) * P) *ᵥ (P⁻¹ *ᵥ v)
          = ((P⁻¹ * M ^ (k : ℕ) * P) * P⁻¹) *ᵥ v := (Matrix.mulVec_mulVec _ _ _)
        _ = (P⁻¹ * M ^ (k : ℕ)) *ᵥ v := by
          rw [Matrix.mul_assoc _ P, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
        _ = _ := (Matrix.mulVec_mulVec _ _ _).symm
    rw [krylov_apply, pow_conj M P hP, e]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov_apply]
  rw [kdet, kdet, hk, Matrix.det_mul]
  have h1 : P⁻¹.det * P.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hP, Matrix.det_one]
  rw [mul_assoc, mul_comm (krylov M v).det, ← mul_assoc, h1, one_mul]

/-- **Z0.2.** -/
theorem krylov_diagonal (d y : Fin n → R) : krylov (diagonal d) y = diagonal y * vandermonde d := by
  refine Matrix.ext fun i k => ?_
  rw [krylov_apply, Matrix.diagonal_pow, Matrix.mulVec_diagonal, Matrix.diagonal_mul]
  simp [Matrix.vandermonde_apply, mul_comm]

theorem kdet_diagonal (d y : Fin n → R) :
    kdet (diagonal d) y = (∏ i, y i) * ∏ i, ∏ j ∈ Ioi i, (d j - d i) := by
  rw [kdet, krylov_diagonal, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]

/-- **Z0.3.** -/
theorem eq_diagonal_of_commute (M : Matrix (Fin n) (Fin n) R) (η : Fin n → R)
    (hη : Pairwise fun i j => IsUnit (η i - η j)) (hc : M * diagonal η = diagonal η * M) :
    M = diagonal fun i => M i i := by
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij; simp
  · have h := congrFun (congrFun hc i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h2 : (η j - η i) * M i j = 0 := by linear_combination h
    have hu : IsUnit (η j - η i) := hη (Ne.symm hij)
    simp [hij, (hu.mul_right_eq_zero).1 h2]

/-- **Z0.5.** -/
theorem kdet_mul_vdm (T Y P : Matrix (Fin n) (Fin n) R) (η : Fin n → R)
    (hP : IsUnit P.det) (hY : Y * P = P * diagonal η)
    (hη : Pairwise fun i j => IsUnit (η i - η j))
    (hTY : Commute T Y) (v : Fin n → R) :
    P⁻¹ * T * P = diagonal (fun i => (P⁻¹ * T * P) i i) ∧
    kdet T v * (∏ i, ∏ j ∈ Ioi i, (η j - η i))
      = kdet Y v * ∏ i, ∏ j ∈ Ioi i, ((P⁻¹ * T * P) j j - (P⁻¹ * T * P) i i) := by
  have hY' : P⁻¹ * Y * P = diagonal η := by
    rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  have hc : (P⁻¹ * T * P) * diagonal η = diagonal η * (P⁻¹ * T * P) := by
    rw [← hY']
    calc P⁻¹ * T * P * (P⁻¹ * Y * P) = P⁻¹ * (T * Y) * P := by
          rw [show P⁻¹ * T * P * (P⁻¹ * Y * P) = P⁻¹ * T * (P * P⁻¹) * Y * P by
            simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hP]
          simp [Matrix.mul_assoc]
      _ = P⁻¹ * (Y * T) * P := by rw [hTY.eq]
      _ = _ := by
          rw [show P⁻¹ * Y * P * (P⁻¹ * T * P) = P⁻¹ * Y * (P * P⁻¹) * T * P by
            simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hP]
          simp [Matrix.mul_assoc]
  have hdiag := eq_diagonal_of_commute _ η hη hc
  refine ⟨hdiag, ?_⟩
  set τ := fun i => (P⁻¹ * T * P) i i
  have e1 := kdet_conj T P hP v
  have e2 := kdet_conj Y P hP v
  rw [hdiag, kdet_diagonal] at e1
  rw [hY', kdet_diagonal] at e2
  rw [← e1, ← e2]
  ring

end CatalanCore.Bordered
