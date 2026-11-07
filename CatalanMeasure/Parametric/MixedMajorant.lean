module
public import CatalanMeasure.Parametric.RealSheetBounds
public import CatalanMeasure.PinMajorant
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set OAI.InternalCatalan
open scoped BigOperators
noncomputable section

noncomputable def paramPinRowFun (P : Parameters) (N : ℕ) {k : ℕ} (r : Fin k) (t : ℝ) : ℝ := realRowAmplitude P N r.val t

/-- Column functions: the filtered columns with exponents `E i`. -/
noncomputable def paramPinColFun (P : Parameters) (N : ℕ) {p : ℕ} (E : Fin p → ℕ) (i : Fin p) (s : ℝ) : ℝ :=
  (filteredColumn P N (E i)).eval s

/-- The Cauchy kernel. -/
noncomputable def paramPinKernel (t s : ℝ) : ℝ := 1 / (1 - t * s)

/-- The weight of a row node in the sheet factorization. -/
noncomputable def paramRowNodeWeight (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  |realCoordinateInv x| ^ (P.C N - 1) * (1 - realCoordinateInv x) ^ P.h N

/-- The `p`-node principal integrand (OpenAI's `realPrincipalIntegrand` with `p` nodes). -/
noncomputable def paramPinPrincipal (P : Parameters) (N : ℕ) {p : ℕ} (x s : Fin p → ℝ) : ℝ :=
  (∏ i, paramRowNodeWeight P N (x i)) *
    |∏ i, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
    |∏ i, ∏ j ∈ Ioi i, (s j - s i)| ^ 2 /
    (∏ i, ∏ j, (1 - realCoordinateInv (x i) * s j)) *
    ∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N)

theorem paramRowNodeWeight_nonneg (P : Parameters) (N : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ paramRowNodeWeight P N x :=
  mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (one_sub_realCoordinateInv_pos hx).le _)

theorem paramPinPrincipal_nonneg (P : Parameters) (N : ℕ) {p : ℕ} (x s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    0 ≤ paramPinPrincipal P N x s := by
  unfold paramPinPrincipal
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (mul_nonneg (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hx i))
        (abs_nonneg _)) (pow_nonneg (abs_nonneg _) _)
    · exact prod_nonneg fun i _ => prod_nonneg fun j _ => (realCoordinateInv_kernel_pos _ (hs j)).le
  · exact prod_nonneg fun j _ =>
      mul_nonneg (pow_nonneg (hs j).1.le _) (pow_nonneg (sub_pos.mpr (hs j).2).le _)

/-- The row determinant through OpenAI's sheet determinant. -/
theorem param_abs_rowDet_eq_sheet {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) {p m : ℕ} (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (hz : ∀ c, Fin.append x y c ∈ Ioo (-1 : ℝ) 1)
    (hz0 : ∀ c, Fin.append x y c ≠ 0) :
    |CatalanMeasure.rowDet (paramPinRowFun P N) (realCoordinateInv ∘ y) (realCoordinateInv ∘ x)| =
      |realSheetDeterminant P N (fun c => Fin.append x y (Fin.cast hpm.symm c))| *
        (∏ i, paramRowNodeWeight P N (x i)) * ∏ j, paramRowNodeWeight P N (y j) := by
  set z : Fin (P.n N) → ℝ := fun c => Fin.append x y (Fin.cast hpm.symm c) with hzdef
  have hzm : ∀ c, z c ∈ Ioo (-1 : ℝ) 1 := fun c => hz _
  have hz0' : ∀ c, z c ≠ 0 := fun c => hz0 _
  have hrow : CatalanMeasure.rowDet (paramPinRowFun P N) (realCoordinateInv ∘ y)
      (realCoordinateInv ∘ x) =
      Matrix.det (Matrix.of (fun r i : Fin (P.n N) =>
        realRowAmplitude P N r.val (realCoordinateInv (z i)))) := by
    unfold CatalanMeasure.rowDet
    rw [fin_append_comp, ← det_fin_cast hpm]
    rfl
  rw [hrow, realRowAmplitude_det_eq_sheet hP hN z hzm hz0', abs_mul, abs_prod]
  have hw : ∀ c, |realCoordinateInv (z c) ^ (P.C N - 1) *
      (1 - realCoordinateInv (z c)) ^ P.h N| = paramRowNodeWeight P N (z c) := by
    intro c
    rw [abs_mul, abs_pow, abs_pow, abs_of_pos (one_sub_realCoordinateInv_pos (hzm c))]
    rfl
  simp_rw [hw]
  rw [mul_assoc]
  congr 1
  rw [hzdef, prod_fin_cast hpm (fun c => paramRowNodeWeight P N (Fin.append x y c)),
    Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end
end CatalanMeasure.Parametric
