module

public import CatalanFrames.Thirds.ContourInstances
public import CatalanFrames.P6.Const
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

/-! # Target constants of the two thirds frames

These series identities depend only on the frame data, without a numerical decay certificate.
-/

open CatalanCore CatalanFrames.P6

namespace CatalanFrames.Thirds

/-- `ζ(2, 2/3) = 9 b`. -/
theorem hurwitz_two_thirds :
    hurwitzTail2 (2 / 3) = 9 * ∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
  unfold hurwitzTail2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  have : (3 : ℝ) * k + 2 ≠ 0 := by positivity
  have : (k : ℝ) + 2 / 3 ≠ 0 := by positivity
  field_simp
  norm_num

theorem thirds_series_facts :
    (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2) + (∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)
      = 4 * Real.pi ^ 2 / 27 := by
  have h := split_three
  rw [hasSum_zeta_two.tsum_eq] at h
  linarith

theorem thirdsAc_const :
    thirdsAc.const = (-1 / 2 : ℚ) * (chi3L2 + Real.pi ^ 2 / 9) := by
  have e : thirdsAc.const = (∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) *
      hurwitzTail2 (![1 / 3, 1] i)) / ((9 : ℚ) : ℝ) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hurwitz_one, hurwitz_third, chi3L2_eq_sub, hasSum_zeta_two.tsum_eq]
  have := thirds_series_facts
  generalize (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2) = a at *
  generalize (∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2) = b at *
  push_cast
  linarith

theorem thirdsBc_const :
    thirdsBc.const = (1 / 2 : ℚ) * (chi3L2 - Real.pi ^ 2 / 9) := by
  have e : thirdsBc.const = (∑ i : Fin 2, ((![-1, 1] i : ℤ) : ℝ) *
      hurwitzTail2 (![2 / 3, 1] i)) / ((9 : ℚ) : ℝ) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hurwitz_one, hurwitz_two_thirds, chi3L2_eq_sub, hasSum_zeta_two.tsum_eq]
  have := thirds_series_facts
  generalize (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2) = a at *
  generalize (∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2) = b at *
  push_cast
  linarith

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.thirdsAc_const
#print axioms CatalanFrames.Thirds.thirdsBc_const
