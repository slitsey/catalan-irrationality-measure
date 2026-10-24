module

public import CatalanMeasure.Parametric.MarkedSheetHadamard
public import CatalanArchive.CatalanMeasure.Parametric.TwentyMarkedEnergyProducts

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Finset Polynomial
open scoped BigOperators Topology

noncomputable section

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
    simp only [actualLaurentEntry, rowOffset, neg_sub]
  · simp only [markedPhysicalMatrix, hmi, ↓reduceIte, Matrix.of_apply,
      markedLaurentMatrix]
    rw [rowP_realCoordinateInv_signed hP hN r.isLt (hx0 i)]
    simp only [rowOffset, neg_sub]
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

theorem marked_sheet_product_first_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) :
    markedSheetProduct P N hpm x y s ≤
      ((3 / 2 : ℝ) ^ P.n N * (P.n N : ℝ) ^ ((P.n N : ℝ) / 2)) *
        firstMarkedProduct P N hpm x y s := by
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  have hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    change Fin.append x y (Fin.cast hpm.symm i) ∈ Ioo (-1 : ℝ) 1
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j)
      (Fin.cast hpm.symm i)
  have hz0 : ∀ i, z i ≠ 0 := by
    intro i
    change Fin.append x y (Fin.cast hpm.symm i) ≠ 0
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j)
      (Fin.cast hpm.symm i)
  have hsheet := marked_laurent_hadamard hP hN z marked hz hz0
  have hprod : 0 ≤ (∏ i, (1 + s i)) ^ m :=
    pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _
  have hfixed : 0 ≤ ∏ j, paramRowNodeWeight P N (y j) :=
    prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)
  have hprincipal := paramPinPrincipal_nonneg P N x s hx hs
  have hcommon : 0 ≤ ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| :=
    prod_nonneg fun j _ => abs_nonneg _
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsheet hprod) hfixed) hprincipal) hcommon
  convert hh using 1
  · rfl
  · unfold firstMarkedProduct populationOneProduct paramSheetOneWeight
    dsimp only [z]
    ring

theorem twenty_first_marked_sheet_product_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      markedSheetProduct twenty N hpm x y s ≤
        ((3 / 2 : ℝ) ^ twenty.n N * (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2)) *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
            90 * N * m) := by
  filter_upwards [twenty_first_marked_product_eventually hε,
      Filter.eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  exact (marked_sheet_product_first_le twenty_admissible hN hpm x y s hx hx0 hy hy0 hs).trans
    (mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase)
      (by positivity))

end
end CatalanMeasure.Parametric
