module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Z0.9: counting eigenvalues equal to one in a pencil
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

variable {L : Type*} [Field L] {n : ℕ}

open scoped Classical in
/-- If `M F = B F diag μ` with `B, F` invertible, then `#{i | μ i = 1} + rank (M - B) = n`. -/
theorem card_eq_one_eq (M B F : Matrix (Fin n) (Fin n) L) (μ : Fin n → L)
    (hB : IsUnit B.det) (hF : IsUnit F.det) (h : M * F = B * F * diagonal μ) :
    (univ.filter fun i => μ i = 1).card + (M - B).rank = n := by
  have h1 : (M - B) * F = (B * F) * diagonal (fun i => μ i - 1) := by
    rw [Matrix.sub_mul, h, Matrix.mul_assoc B F, Matrix.mul_assoc B F]
    have : diagonal (fun i => μ i - 1) = diagonal μ - 1 := by
      refine Matrix.ext fun a b => ?_
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab]
    rw [this, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sub]
  have hBF : IsUnit (B * F).det := by rw [Matrix.det_mul]; exact hB.mul hF
  have h2 : (M - B).rank = (diagonal (fun i => μ i - 1)).rank := by
    rw [← rank_mul_eq_left_of_isUnit_det F _ hF, h1, rank_mul_eq_right_of_isUnit_det _ _ hBF]
  rw [h2, rank_diagonal, Fintype.card_subtype]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => μ i = 1)
  simpa [sub_eq_zero] using this

end CatalanCore.Bordered
