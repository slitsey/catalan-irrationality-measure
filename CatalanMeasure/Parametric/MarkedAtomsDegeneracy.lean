module

public import CatalanMeasure.Parametric.MarkedMixedMajorant

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan

noncomputable section

/-- Duplicate original P-only atoms give identical fixed columns. This does
not assert any collision zero between positive atoms and actual free nodes. -/
theorem original_poly_atoms_rowDet_eq_zero_of_not_injective (P : Parameters)
    (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) (t : Fin p → ℝ)
    (hi : ¬Function.Injective y) :
    CatalanMeasure.rowDetWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y) t = 0 := by
  unfold Function.Injective at hi
  push Not at hi
  obtain ⟨j, j', hy, hne⟩ := hi
  unfold CatalanMeasure.rowDetWithAtoms
  apply Matrix.det_zero_of_column_eq
    (show Fin.natAdd p j ≠ Fin.natAdd p j' from fun he => hne (Fin.natAdd_injective _ _ he))
  intro r
  simp only [Matrix.of_apply, Fin.addCases_right, originalPolyAtoms, hy]

theorem original_poly_atoms_mixedDouble_eq_zero_of_not_injective (P : Parameters)
    (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) (t s : Fin p → ℝ) (E : Fin p → ℕ)
    (hi : ¬Function.Injective y) :
    CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel t s = 0 := by
  unfold CatalanMeasure.mixedDoubleWithAtoms
  rw [original_poly_atoms_rowDet_eq_zero_of_not_injective P N y t hi]
  simp only [zero_mul]

end
end CatalanMeasure.Parametric
