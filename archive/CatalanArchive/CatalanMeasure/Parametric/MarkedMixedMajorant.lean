module

public import CatalanMeasure.MixedArbitraryAtoms
public import CatalanArchive.CatalanMeasure.Parametric.MarkedSheetPhysical

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Finset Set OAI.InternalCatalan
open scoped BigOperators

noncomputable section

def originalPolyAtoms (P : Parameters) (N : ℕ) {p m : ℕ} (y : Fin m → ℝ) :
    Fin (p + m) → Fin m → ℝ :=
  fun r j => (realPoly (rowP P N r)).eval (realCoordinateInv (y j))

theorem original_poly_atoms_rowDet_factor {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0) :
    |CatalanMeasure.rowDetWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
        (realCoordinateInv ∘ x)| =
      (∏ i : Fin (P.n N), paramRowNodeWeight P N
        (Fin.append x y (Fin.cast hpm.symm i))) *
      |(markedLaurentMatrix (P.g N)
        (fun i => Fin.append x y (Fin.cast hpm.symm i))
        (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| := by
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
  have hm : (Matrix.of fun r c : Fin (p + m) =>
      Fin.addCases (fun i => paramPinRowFun P N r ((realCoordinateInv ∘ x) i))
        (fun j => originalPolyAtoms P N y r j) c).submatrix
        (finCongr hpm.symm) (finCongr hpm.symm) =
      (markedPhysicalMatrix P N z marked).transpose := by
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply,
      markedPhysicalMatrix, finCongr_apply]
    generalize hc : Fin.cast hpm.symm c = c'
    cases c' using Fin.addCases with
    | left i => simp [marked, z, hc, paramPinRowFun]
    | right j => simp [marked, z, hc, originalPolyAtoms]
  rw [CatalanMeasure.rowDetWithAtoms,
    ← Matrix.det_submatrix_equiv_self (finCongr hpm.symm), hm, Matrix.det_transpose]
  exact marked_physical_det_factor hP hN z marked hz hz0

/-- The selected filtered-column and Cauchy factors do not depend on the atom
row type. This is the original/P-only counterpart of MixedMajorant. -/
theorem original_poly_atoms_mixedDouble_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| ≤
      (∏ j : Fin p, (1 + s j)) ^ m *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s := by
  have hrow := original_poly_atoms_rowDet_factor hP hN hpm x y hx hx0 hy hy0
  have hw : (∏ i : Fin (P.n N), paramRowNodeWeight P N
      (Fin.append x y (Fin.cast hpm.symm i))) =
      (∏ i, paramRowNodeWeight P N (x i)) * ∏ j, paramRowNodeWeight P N (y j) := by
    rw [prod_fin_cast hpm (fun c => paramRowNodeWeight P N (Fin.append x y c)),
      Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hw] at hrow
  have ht : ∀ i, (realCoordinateInv ∘ x) i ∈ Ioo (-1 : ℝ) 1 :=
    fun i => realCoordinateInv_mem (hx i)
  have hD : 0 < ∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j) :=
    prod_pos fun i _ => prod_pos fun j _ => realCoordinateInv_kernel_pos _ (hs j)
  have hK : (Matrix.of fun i j : Fin p => paramPinKernel ((realCoordinateInv ∘ x) i) (s j)).det =
      ((∏ i : Fin p, ∏ j ∈ Ioi i, ((realCoordinateInv ∘ x) j - (realCoordinateInv ∘ x) i)) *
        (∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i))) /
        (∏ i : Fin p, ∏ j : Fin p, (1 - (realCoordinateInv ∘ x) i * s j)) :=
    realCauchy_det_eq_prod _ s ht hs
  have hG : (Matrix.of fun j i : Fin p => paramPinColFun P N E i (s j)).det =
      (∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
        (Matrix.of fun l i : Fin p => s l ^ E i).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext j i
    simp only [paramPinColFun, filteredColumn, Matrix.of_apply, eval_mul,
      eval_pow, eval_X, eval_sub, eval_one]
    ring
  have hsw : 0 ≤ ∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N) :=
    prod_nonneg fun j _ => mul_nonneg (pow_nonneg (hs j).1.le _)
      (pow_nonneg (sub_pos.mpr (hs j).2).le _)
  have hGV := CatalanMeasure.genVandermonde_abs_le_product s
    (fun j => ⟨(hs j).1.le, (hs j).2.le⟩) E hE hEn
  have hm : P.n N - p = m := by omega
  rw [hm] at hGV
  have hGb : |(Matrix.of fun j i : Fin p => paramPinColFun P N E i (s j)).det| ≤
      (∏ j, (s j ^ P.b N * (1 - s j) ^ P.q N)) *
        ((∏ j : Fin p, (1 + s j)) ^ m * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)|) := by
    rw [hG, abs_mul, abs_of_nonneg hsw]
    exact mul_le_mul_of_nonneg_left hGV hsw
  have hKabs : |(Matrix.of fun i j : Fin p => paramPinKernel ((realCoordinateInv ∘ x) i) (s j)).det| =
      |∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j)) := by
    rw [hK, abs_div, abs_mul]
    simp only [Function.comp_apply, abs_of_pos hD]
  unfold CatalanMeasure.mixedDoubleWithAtoms
  rw [abs_mul, abs_mul, hrow, hKabs]
  have hleft : 0 ≤ ((∏ i, paramRowNodeWeight P N (x i)) *
      (∏ j, paramRowNodeWeight P N (y j)) *
      |(markedLaurentMatrix (P.g N)
        (fun i => Fin.append x y (Fin.cast hpm.symm i))
        (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det|) *
      (|∏ i : Fin p, ∏ j ∈ Ioi i, (realCoordinateInv (x j) - realCoordinateInv (x i))| *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| /
          (∏ i : Fin p, ∏ j : Fin p, (1 - realCoordinateInv (x i) * s j))) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (prod_nonneg fun i _ => paramRowNodeWeight_nonneg P N (hx i))
      (prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j))) (abs_nonneg _))
      (div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD.le)
  have hb := mul_le_mul_of_nonneg_left hGb hleft
  convert hb using 1
  unfold paramPinPrincipal
  ring

theorem original_poly_atoms_mixedDouble_mul_weight_le {P : Parameters} (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) (β : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) {Q : ℝ}
    (hweight : ∀ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| ≤ Q) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| * (∏ j, |β j|) ≤
      markedSheetProduct P N hpm x y s * Q ^ m := by
  let C := ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|
  have hc (j : Fin m) : 0 < |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hC : 0 < C := prod_pos fun j _ => hc j
  have hp : 0 ≤ markedSheetProduct P N hpm x y s := by
    unfold markedSheetProduct
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg
        (pow_nonneg (prod_nonneg fun i _ => by linarith [(hs i).1]) _) (abs_nonneg _))
        (prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)
    · exact hC.le
  have hbase := original_poly_atoms_mixedDouble_le hP hN hpm E hE hEn x y s hx hx0 hy hy0 hs
  have hprod : (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j|) ≤ Q ^ m := by
    calc
      _ ≤ ∏ _j : Fin m, Q := prod_le_prod₀
        (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (fun j _ => hweight j)
      _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]
  have heq : markedSheetProduct P N hpm x y s *
      (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j|) =
      ((∏ j : Fin p, (1 + s j)) ^ m *
        |(markedLaurentMatrix (P.g N)
          (fun i => Fin.append x y (Fin.cast hpm.symm i))
          (fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i))).det| *
        (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s) * ∏ j, |β j| := by
    rw [prod_mul_distrib]
    unfold markedSheetProduct
    change (_ / C) * (C * _) = _
    rw [← mul_assoc, div_mul_cancel₀ _ hC.ne']
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase (prod_nonneg fun j _ => abs_nonneg _)
    _ = _ := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hp

end
end CatalanMeasure.Parametric
