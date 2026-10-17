module

public import CatalanArchive.CatalanMeasure.Parametric.DigitDisplacement
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Polynomial shifts in the actual digit functional

The moment and zeta weights are the concrete rational functions used by the
leading-residue formula. Between carries a polynomial shift is exact; at a
carry the defect factors as a row scalar times 1/(k+1).
-/

@[expose] public section

namespace CatalanMeasure.Parametric

set_option autoImplicit false

open Polynomial OAI.InternalCatalan
open scoped BigOperators

def leadingBlock (p B ell k : ℕ) (Q D : ℚ[X]) : ℚ :=
  ∑ v ∈ Finset.range (B + 1),
    (Q.coeff (v * p + ell) * digitMoment v k -
      (3 / 2 : ℚ) * D.coeff (v * p + ell) * zetaRat v k)

theorem leadingBlock_shift_noncarry (p B ell k : ℕ) (Q D : ℚ[X]) :
    leadingBlock p B (ell + 1) k (X * Q) (X * D) =
      leadingBlock p B ell k Q D := by
  unfold leadingBlock
  apply Finset.sum_congr rfl
  intro v hv
  simp only [← Nat.add_assoc, coeff_X_mul]

theorem leadingBlock_shift_carry {p B : ℕ} (hp : 0 < p) (k : ℕ)
    (Q D : ℚ[X]) (hQ : Q.natDegree < B * p) (hD : D.natDegree < B * p) :
    leadingBlock p B 0 (k + 1) (X * Q) (X * D) -
      leadingBlock p B (p - 1) k Q D =
    (∑ v ∈ Finset.range B,
      (-(if v = 0 then 0 else Q.coeff (v * p + (p - 1)) * momentScalar (v - 1)) +
        (3 / 2 : ℚ) * D.coeff (v * p + (p - 1)) / ((v + 1 : ℕ) : ℚ))) /
      ((k + 1 : ℕ) : ℚ) := by
  have hindex (v : ℕ) : (v + 1) * p = (v * p + (p - 1)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have htailQ : Q.coeff (B * p + (p - 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have htailD : D.coeff (B * p + (p - 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hshift : leadingBlock p B 0 (k + 1) (X * Q) (X * D) =
      ∑ v ∈ Finset.range B,
        (Q.coeff (v * p + (p - 1)) * digitMoment (v + 1) (k + 1) -
          (3 / 2 : ℚ) * D.coeff (v * p + (p - 1)) * zetaRat (v + 1) (k + 1)) := by
    unfold leadingBlock
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul, zero_add, coeff_X_mul_zero, zero_mul, mul_zero,
      sub_self, add_zero]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hindex, coeff_X_mul, coeff_X_mul]
  have hbase : leadingBlock p B (p - 1) k Q D =
      ∑ v ∈ Finset.range B,
        (Q.coeff (v * p + (p - 1)) * digitMoment v k -
          (3 / 2 : ℚ) * D.coeff (v * p + (p - 1)) * zetaRat v k) := by
    unfold leadingBlock
    rw [Finset.sum_range_succ]
    simp [htailQ, htailD]
  rw [hshift, hbase, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ v ∈ Finset.range B,
        (Q.coeff (v * p + (p - 1)) * (digitMoment (v + 1) (k + 1) - digitMoment v k) -
          (3 / 2 : ℚ) * D.coeff (v * p + (p - 1)) *
            (zetaRat (v + 1) (k + 1) - zetaRat v k)) := by
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := carryBlock_factor B k
      (fun v => Q.coeff (v * p + (p - 1)))
      (fun v => D.coeff (v * p + (p - 1)))

end CatalanMeasure.Parametric
