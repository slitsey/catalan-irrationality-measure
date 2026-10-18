module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-!
# Nonvanishing of the Cauchy determinant (two-family form, any field)

If `x` and `y` are injective families in a field with `x i + y j ≠ 0`, then
`det [1/(x i + y j)] ≠ 0`.  (Polynomial interpolation argument.)
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore

theorem cauchy_det_ne_zero {F : Type*} [Field F] {n : ℕ} (x y : Fin n → F)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i + y j ≠ 0) :
    (Matrix.of fun i j => 1 / (x i + y j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv0
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact funext fun i => i.elim0
  set P : F[X] := ∑ j : Fin n, C (v j) * ∏ i ∈ univ.erase j, (X + C (y i)) with hP
  have hdeg : P.natDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := n - 1) _ _ ?_) (by omega)
    intro j _
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ univ.erase j, (X + C (y i)).natDegree
        ≤ ∑ i ∈ univ.erase j, 1 := by
          apply Finset.sum_le_sum; intro i _; exact (natDegree_X_add_C _).le
      _ = n - 1 := by simp
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hx ?_ hdeg
    intro a
    have h1 := congrFun hv a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    have h2 : P.eval (x a) = (∏ i : Fin n, (x a + y i)) * ∑ j : Fin n, 1 / (x a + y j) * v j := by
      rw [hP, eval_finsetSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_mul, eval_C, eval_prod]
      simp only [eval_add, eval_X, eval_C]
      have := Finset.mul_prod_erase (univ : Finset (Fin n)) (fun i => x a + y i)
        (Finset.mem_univ j)
      rw [← this]
      field_simp [hxy a j]
    rw [h2, h1, mul_zero]
  funext j
  have h3 := congrArg (Polynomial.eval (-(y j))) hP0
  rw [hP, eval_finsetSum, eval_zero] at h3
  rw [Finset.sum_eq_single j] at h3
  · rw [eval_mul, eval_C, eval_prod] at h3
    simp only [eval_add, eval_X, eval_C] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · simpa using h
    · exfalso
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨i, hi, hzero⟩ := h
      have hij : i ≠ j := (Finset.mem_erase.1 hi).1
      have : y i = y j := by linear_combination hzero
      exact hij (hy this)
  · intro j' _ hj'
    rw [eval_mul, eval_C, eval_prod]
    simp only [eval_add, eval_X, eval_C]
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨Ne.symm hj', mem_univ j⟩) (by ring)]
    simp
  · simp

end CatalanCore
