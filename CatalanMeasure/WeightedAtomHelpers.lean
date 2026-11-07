module

public import CatalanMeasure.MixedAndreief
public import OAI.NumberTheory.Catalan.Analysis.RealPairedIntegral

@[expose] public section

/-!
# Two measure and determinant facts used by the weighted atom bound

`abs_det_submatrix_equiv` (a row and column reindexing of a square matrix keeps `|det|`) and
`pairMeasure_real_univ` (the pair measure of the real place and `(0,1)` has total mass `2 ^ p`),
moved unchanged from `CatalanMeasure.Lemma6`, so that `WeightedAtom` no longer imports the
`Lemma6` / `DualTwo` chain.
-/

namespace OAI.InternalCatalan
open Finset Set Filter Polynomial
open scoped BigOperators Nat
noncomputable section
theorem abs_det_submatrix_equiv {k l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ) (g e : Fin k ≃ Fin l) :
    |(M.submatrix g e).det| = |M.det| := by
  have h : M.submatrix g e = (M.submatrix id (g.symm.trans e)).submatrix g g := by
    ext r c
    simp
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_permute', abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (g.symm.trans e)) with hs | hs <;> simp [hs]

theorem pairMeasure_real_univ (p : ℕ) :
    (CatalanMeasure.pairMeasure realPlaceMeasure
        (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) p).real Set.univ = 2 ^ p := by
  unfold CatalanMeasure.pairMeasure
  rw [MeasureTheory.measureReal_def, ← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.pi_univ, MeasureTheory.Measure.pi_univ]
  simp [realPlaceMeasure_univ, Real.volume_Ioo]

end
end OAI.InternalCatalan
