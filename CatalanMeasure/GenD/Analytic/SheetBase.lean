module

public import CatalanMeasure.Parametric.MarkedSheetHadamard
public import CatalanMeasure.Parametric.MixedMajorant
public import CatalanMeasure.Parametric.RestrictedQuadrature
public import CatalanMeasure.Parametric.RestrictedWeights
public import CatalanMeasure.Parametric.CommonFactor

@[expose] public section

/-!
# Analytic layer, group 3: restated sheet base (G2 stand-ins)

Design-generic restatements, with the same bodies, of the clean-but-dirty-imported pieces that the
weighted-atom layer needs: `markedPhysicalMatrix`, `markedSheetProduct` (from
`MarkedSheetPhysical`), `rowCommonFactor_eval_ne_zero_of`, `filteredCatalanCoeff_full_weights`
(from `FullIntervalFormula`), and the sheet prefactor.

INTEGRATION NOTE: group 2 restates `markedSheetProduct`/`sheetPrefactor` in its own files; at the
merge this file is reduced to whatever group 2 does not already provide (the declarations are
identical, so the replacement is a rename of the import).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Finset Set OAI.InternalCatalan CatalanMeasure.Parametric
open scoped BigOperators

noncomputable section

/-- The sheet prefactor `(3/2)^n n^(n/2) + (1 + 10 e^12 n)^n` (`n = P.n N`). -/
def sheetPrefactor (P : Parameters) (N : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2) +
    (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N

/-- Node-first matrix of actual free rows and original polynomial marked rows. -/
def markedPhysicalMatrix (P : Parameters) (N : ℕ) (x : Fin (P.n N) → ℝ)
    (marked : Fin (P.n N) → Bool) : Matrix (Fin (P.n N)) (Fin (P.n N)) ℝ :=
  Matrix.of fun i r => if marked i then
    (realPoly (rowP P N r)).eval (realCoordinateInv (x i))
    else realRowAmplitude P N r (realCoordinateInv (x i))

theorem marked_physical_matrix_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    markedPhysicalMatrix P N x marked = Matrix.of (fun i r =>
      ((1 - realCoordinateInv (x i)) ^ P.h N *
        realCoordinateInv (x i) ^ (P.C N - 1)) *
          markedLaurentMatrix (P.g N) x marked i r) := by
  ext i r
  cases hmi : marked i
  · simp only [markedPhysicalMatrix, hmi, Bool.false_eq_true, ↓reduceIte,
      Matrix.of_apply, markedLaurentMatrix]
    rw [realRowAmplitude_sheet hP hN r.isLt (hx i) (hx0 i)]
    simp only [actualLaurentEntry, Parametric.rowOffset, neg_sub]
  · simp only [markedPhysicalMatrix, hmi, ↓reduceIte, Matrix.of_apply,
      markedLaurentMatrix]
    rw [rowP_realCoordinateInv_signed hP hN r.isLt (hx0 i)]
    simp only [Parametric.rowOffset, neg_sub]
    ring

theorem marked_physical_det_factor {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (x : Fin (P.n N) → ℝ) (marked : Fin (P.n N) → Bool)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0) :
    |(markedPhysicalMatrix P N x marked).det| =
      (∏ i, paramRowNodeWeight P N (x i)) *
        |(markedLaurentMatrix (P.g N) x marked).det| := by
  rw [marked_physical_matrix_factor hP hN x marked hx hx0,
    Matrix.det_mul_column, abs_mul, abs_prod]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [abs_mul, abs_pow, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hx i))]
  unfold paramRowNodeWeight
  ring

/-- The normalized sheet part of an arbitrary selected-column mixed integrand.
The kernel/column determinant estimate is independent of the marked row type. -/
def markedSheetProduct (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  (∏ i, (1 + s i)) ^ m * |(markedLaurentMatrix (P.g N) z marked).det| *
    (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

theorem rowCommonFactor_eval_ne_zero_of (P : Parameters) (N : ℕ) {t : ℝ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (rowCommonFactor P N).eval t ≠ 0 := by
  simp only [rowCommonFactor, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1.symm))

theorem filteredCatalanCoeff_full_weights {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0 < N) (hr : r < P.n N) {J : ℕ} (hJ : P.n N - P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ)
    (hτ0 : ∀ a, τ a ≠ 0) (hτ1 : ∀ a, τ a ≠ 1) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k : ℝ) =
      ∑ a, (realPoly (rowP P N r)).eval (τ a) * restrictedWeight P N k τ a := by
  rw [filteredCatalanCoeff_restricted_quadrature hP hN hr hJ hτ]
  apply sum_congr rfl
  intro a _
  have he : (realPoly (rowP P N r)).eval (τ a) =
      (rowCommonFactor P N).eval (τ a) * (realPoly (rowResidualP P N r)).eval (τ a) := by
    rw [rowP_common_factor hP hN hr]
    simp [realPoly, rowCommonFactor]
  have hn := rowCommonFactor_eval_ne_zero_of P N (hτ0 a) (hτ1 a)
  rw [he, restrictedWeight]
  field_simp

end

end Analytic
end CatalanMeasure.GenD
