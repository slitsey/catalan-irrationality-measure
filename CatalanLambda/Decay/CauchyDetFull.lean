import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The Cauchy determinant over a field

`det [1/(x_i - y_j)] = ∏_{i<j} (x_j - x_i)(y_i - y_j) / ∏_{i,j} (x_i - y_j)`.
-/

open Finset Matrix Polynomial

namespace CatalanLambda.Decay

variable {K : Type*} [Field K] {n : ℕ}

/-- Lagrange-type polynomials `p_j = ∏_{k ≠ j} (X - y_k)`. -/
noncomputable def lagP (y : Fin n → K) (j : Fin n) : K[X] :=
  ∏ k ∈ univ.erase j, (X - C (y k))

lemma lagP_natDegree_lt (y : Fin n → K) (j : Fin n) : (lagP y j).natDegree < n := by
  unfold lagP
  refine lt_of_le_of_lt (natDegree_prod_le _ _) ?_
  simp [Finset.card_erase_of_mem]
  have := j.2; omega

/-- Coefficient matrix of the `p_j`. -/
noncomputable def lagCoef (y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun m j => (lagP y j).coeff m

lemma vandermonde_mul_lagCoef (t y : Fin n → K) (i j : Fin n) :
    (vandermonde t * lagCoef y) i j = (lagP y j).eval (t i) := by
  rw [eval_eq_sum_range' (lagP_natDegree_lt y j), ← Fin.sum_univ_eq_sum_range
    (fun m => (lagP y j).coeff m * t i ^ m) n]
  simp [Matrix.mul_apply, vandermonde, lagCoef, mul_comm]

lemma lagP_eval_ne (y : Fin n → K) {i j : Fin n} (h : i ≠ j) : (lagP y j).eval (y i) = 0 := by
  unfold lagP
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (by simp)

lemma lagP_eval_self (y : Fin n → K) (j : Fin n) :
    (lagP y j).eval (y j) = ∏ k ∈ univ.erase j, (y j - y k) := by
  unfold lagP
  simp [eval_prod]

lemma vandermonde_y_mul_lagCoef (y : Fin n → K) :
    vandermonde y * lagCoef y = Matrix.diagonal (fun j => (lagP y j).eval (y j)) := by
  ext i j
  rw [vandermonde_mul_lagCoef]
  by_cases h : i = j
  · subst h; simp
  · rw [lagP_eval_ne y h]; simp [h]

lemma prod_erase_eq (y : Fin n → K) :
    ∏ j, ∏ k ∈ univ.erase j, (y j - y k)
      = (vandermonde y).det * ∏ i, ∏ j ∈ Ioi i, (y i - y j) := by
  rw [det_vandermonde]
  have h1 : ∀ j : Fin n, ∏ k ∈ univ.erase j, (y j - y k)
      = (∏ k ∈ Iio j, (y j - y k)) * ∏ k ∈ Ioi j, (y j - y k) := by
    intro j
    have : univ.erase j = Iio j ∪ Ioi j := by
      ext k
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
      exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
    rw [this, Finset.prod_union]
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp at hk hk'; omega
  simp_rw [h1]
  rw [Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_comm' ?_
  intro a b; simp

/-- **Cauchy determinant.** -/
theorem cauchy_det (x y : Fin n → K) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    (Matrix.of fun i j => 1 / (x i - y j)).det
      = (∏ i, ∏ j ∈ Ioi i, ((x j - x i) * (y i - y j))) / ∏ i, ∏ j, (x i - y j) := by
  have hVy : (vandermonde y).det ≠ 0 := det_vandermonde_ne_zero_iff.2 hy
  have hden : ∀ i, ∏ k, (x i - y k) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.2 fun k _ => sub_ne_zero.2 (hxy i k)
  -- C = diag d * (V x * lagCoef y)
  have hC : (Matrix.of fun i j => 1 / (x i - y j)) =
      Matrix.diagonal (fun i => (∏ k, (x i - y k))⁻¹) * (vandermonde x * lagCoef y) := by
    ext i j
    rw [Matrix.diagonal_mul, vandermonde_mul_lagCoef]
    unfold lagP
    rw [eval_prod]
    simp only [eval_sub, eval_X, eval_C, Matrix.of_apply]
    rw [← Finset.mul_prod_erase univ (fun k => x i - y k) (Finset.mem_univ j)]
    have : x i - y j ≠ 0 := sub_ne_zero.2 (hxy i j)
    have h2 : ∏ k ∈ univ.erase j, (x i - y k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => sub_ne_zero.2 (hxy i k)
    field_simp
  have hdiag : (vandermonde y * lagCoef y).det = ∏ j, (lagP y j).eval (y j) := by
    rw [vandermonde_y_mul_lagCoef, det_diagonal]
  rw [det_mul] at hdiag
  have hPm : (lagCoef y).det = (∏ j, (lagP y j).eval (y j)) / (vandermonde y).det := by
    rw [eq_div_iff hVy, mul_comm]; exact hdiag
  rw [hC, det_mul, det_diagonal, det_mul, hPm]
  simp_rw [lagP_eval_self]
  rw [prod_erase_eq, det_vandermonde]
  rw [det_vandermonde] at hVy
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [det_vandermonde] at *
  field_simp
