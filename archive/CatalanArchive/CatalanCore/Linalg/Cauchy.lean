module

public import CatalanCore.Linalg.Schur1

/-!
# The Cauchy determinant, two-family form, over any field

`det [1/(x i + y j)] * ∏ i, ∏ j, (x i + y j) = ∏_{i<j} (x j - x i) (y j - y i)`.
Proof: induction on `n` by one Schur-complement step (`det_eq_schur`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F]

/-- The numerator `∏_{i<j} (x j - x i)(y j - y i)`. -/
def cauchyNum {n : ℕ} (x y : Fin n → F) : F :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j then (x j - x i) * (y j - y i) else 1

theorem cauchy_det_mul : ∀ {n : ℕ} (x y : Fin n → F), (∀ i j, x i + y j ≠ 0) →
    (Matrix.of fun i j => 1 / (x i + y j)).det * ∏ i : Fin n, ∏ j : Fin n, (x i + y j) =
      cauchyNum x y
  | 0, x, y, _ => by simp [cauchyNum]
  | n + 1, x, y, hxy => by
    set B : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => 1 / (x i + y j) with hB
    have h00 : B 0 0 ≠ 0 := one_div_ne_zero (hxy 0 0)
    rw [det_eq_schur B h00]
    set x' : Fin n → F := fun i => x i.succ with hx'
    set y' : Fin n → F := fun i => y i.succ with hy'
    have hS : schurS B = Matrix.diagonal (fun i => (x' i - x 0) / (x' i + y 0)) *
        (Matrix.of fun i j => 1 / (x' i + y' j)) *
        Matrix.diagonal (fun j => (y' j - y 0) / (x 0 + y' j)) := by
      ext i j
      have h1 := hxy i.succ 0
      have h2 := hxy 0 j.succ
      have h3 := hxy i.succ j.succ
      have h4 := hxy 0 0
      simp only [schurS, hB, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, hx', hy']
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      field_simp
      ring
    have ih := cauchy_det_mul x' y' (fun i j => hxy _ _)
    rw [hS, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    have hprod : ∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (x i + y j) =
        ((x 0 + y 0) * ∏ j : Fin n, (x 0 + y' j)) *
          ((∏ i : Fin n, (x' i + y 0)) * ∏ i : Fin n, ∏ j : Fin n, (x' i + y' j)) := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.prod_univ_succ, Finset.prod_mul_distrib, hx', hy']
    have hnum : cauchyNum x y = (∏ j : Fin n, ((x' j - x 0) * (y' j - y 0))) * cauchyNum x' y' := by
      unfold cauchyNum
      rw [Fin.prod_univ_succ]
      simp [Fin.prod_univ_succ, hx', hy', Fin.succ_lt_succ_iff, Fin.succ_pos]
    rw [hprod, hnum, ← ih, Finset.prod_mul_distrib]
    have hs : x 0 + y 0 ≠ 0 := hxy 0 0
    have hQ : ∏ i : Fin n, (x' i + y 0) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => hxy _ _
    have hR : ∏ j : Fin n, (x 0 + y' j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => hxy _ _
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
    simp only [hB, Matrix.of_apply]
    field_simp

lemma cauchyNum_eq_Ioi {n : ℕ} (x y : Fin n → F) :
    cauchyNum x y = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i)) := by
  unfold cauchyNum
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j; simp

/-- **Cauchy determinant**, two-family form, over any field. -/
theorem cauchy_det {n : ℕ} (x y : Fin n → F) (hxy : ∀ i j, x i + y j ≠ 0) :
    (Matrix.of fun i j => 1 / (x i + y j)).det =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i))) /
        ∏ i : Fin n, ∏ j : Fin n, (x i + y j) := by
  have hden : ∏ i : Fin n, ∏ j : Fin n, (x i + y j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hxy i j
  rw [eq_div_iff hden, ← cauchyNum_eq_Ioi]
  exact cauchy_det_mul x y hxy

end CatalanCore
