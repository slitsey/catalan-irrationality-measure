module

public import OAI.NumberTheory.Catalan.Polynomial.CentralCoefficients
public import Mathlib.Algebra.BigOperators.Field

/-!
# The separable defect at a base-p carry

The extended moment includes the negative-one row. Its simultaneous digit
shift defect, and that of the zeta matrix, have the same column denominator.
Consequently the combined carry term is a single outer product. This file
proves the rational scalar identities; the actual filtered-matrix connection
and the new rank-window estimate require further work.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

set_option autoImplicit false

open OAI.InternalCatalan
open scoped BigOperators

def digitMoment (v k : ℕ) : ℚ :=
  if v = 0 then momentRatNegOne k else momentRat (v - 1) k

theorem digitMoment_step (v k : ℕ) :
    digitMoment (v + 1) (k + 1) - digitMoment v k =
      if v = 0 then 0 else -momentScalar (v - 1) / ((k + 1 : ℕ) : ℚ) := by
  cases v with
  | zero =>
      simp [digitMoment, momentRat_of_lt (Nat.succ_pos k), momentRatNegOne]
  | succ v =>
      simp only [digitMoment, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      have h := momentRat_step v k
      simpa only [neg_sub, neg_div] using congrArg (fun x : ℚ => -x) h

theorem digitZeta_step (v k : ℕ) :
    zetaRat (v + 1) (k + 1) - zetaRat v k =
      -(1 / (((v + 1 : ℕ) : ℚ) * ((k + 1 : ℕ) : ℚ))) := by
  have h := zetaRat_step v k
  linarith

theorem carryScalar_factor (v k : ℕ) (Q D : ℚ) :
    Q * (digitMoment (v + 1) (k + 1) - digitMoment v k) -
      (3 / 2 : ℚ) * D * (zetaRat (v + 1) (k + 1) - zetaRat v k) =
    (-(if v = 0 then 0 else Q * momentScalar (v - 1)) +
      (3 / 2 : ℚ) * D / ((v + 1 : ℕ) : ℚ)) / ((k + 1 : ℕ) : ℚ) := by
  rw [digitMoment_step, digitZeta_step]
  by_cases hv : v = 0
  · simp only [hv, ite_true, zero_add, Nat.cast_one, mul_zero, neg_zero,
      zero_sub, one_mul, div_one]
    ring
  · simp only [hv, ite_false]
    ring

theorem carryBlock_factor (B k : ℕ) (Q D : ℕ → ℚ) :
    (∑ v ∈ Finset.range B,
      (Q v * (digitMoment (v + 1) (k + 1) - digitMoment v k) -
        (3 / 2 : ℚ) * D v * (zetaRat (v + 1) (k + 1) - zetaRat v k))) =
    (∑ v ∈ Finset.range B,
      (-(if v = 0 then 0 else Q v * momentScalar (v - 1)) +
        (3 / 2 : ℚ) * D v / ((v + 1 : ℕ) : ℚ))) / ((k + 1 : ℕ) : ℚ) := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun v _ => carryScalar_factor v k (Q v) (D v))

end CatalanMeasure.Parametric
