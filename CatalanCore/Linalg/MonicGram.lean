module

public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace CatalanCore.Linalg

/-- A unit lower triangular change of basis preserves a Gram determinant. -/
theorem det_monic_basis {K : Type*} [CommRing K] (n : ℕ)
    (H T : Matrix (Fin n) (Fin n) K)
    (htri : ∀ i j, i < j → T i j = 0) (hdiag : ∀ i, T i i = 1) :
    (T * H * T.transpose).det = H.det := by
  have hLower : T.IsLowerTriangular := fun _ _ hij => htri _ _ hij
  have hdet : T.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular T hLower]
    simp only [hdiag, Finset.prod_const_one]
  simp only [Matrix.det_mul, Matrix.det_transpose, hdet, one_mul, mul_one]

end CatalanCore.Linalg
