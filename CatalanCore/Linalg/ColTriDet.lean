module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Determinant under a triangular change of columns

If column `k` of `A` is `d k` times column `k` of `B` plus a combination of earlier columns of `B`,
then `det A = (∏ d) * det B`.  Frame-independent linear algebra, used for Krylov determinants.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The upper triangular change-of-columns matrix. -/
def colTriMat (d : Fin n → R) (c : Fin n → Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j k => (if j = k then d k else 0) + (if j < k then c k j else 0)

lemma colTriMat_det (d : Fin n → R) (c : Fin n → Fin n → R) :
    (colTriMat d c).det = ∏ k, d k := by
  have h : (colTriMat d c).IsUpperTriangular := by
    intro j k hjk
    have h1 : j ≠ k := fun h => by subst h; exact lt_irrefl _ hjk
    have h2 : ¬ j < k := not_lt.mpr hjk.le
    simp [colTriMat, h1, h2]
  rw [Matrix.det_of_isUpperTriangular h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [colTriMat]

/-- Triangular change of columns. -/
theorem det_eq_prod_mul_det_of_colTri (A B : Matrix (Fin n) (Fin n) R) (d : Fin n → R)
    (c : Fin n → Fin n → R)
    (h : ∀ i k, A i k = d k * B i k + ∑ j ∈ Finset.Iio k, c k j * B i j) :
    A.det = (∏ k, d k) * B.det := by
  have hA : A = B * colTriMat d c := by
    ext i k
    rw [h i k, Matrix.mul_apply]
    have e : ∑ j ∈ Finset.Iio k, c k j * B i j = ∑ j, B i j * (if j < k then c k j else 0) := by
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      exact Finset.sum_congr (by ext; simp) fun _ _ => mul_comm _ _
    rw [e]
    simp only [colTriMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ k]
    simp [mul_comm]
  rw [hA, Matrix.det_mul, colTriMat_det, mul_comm]

end CatalanCore
