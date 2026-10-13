module
public import CatalanMeasure.Parametric.TwentyDenominatorAsymptotic
public import CatalanMeasure.Parametric.TwentyBase.Nonvanishing
public import CatalanMeasure.Parametric.Degree
public import CatalanMeasure.IntegerValued
public import CatalanMeasure.SquareNonvanishing
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators Nat
noncomputable section

open Polynomial Filter Real
theorem natDegree_twenty_denom_mul_deltaPoly_le (p : ℕ) :
    (C (twentyDenomBound p : ℚ) * deltaPoly twenty p).natDegree ≤ 18 * p :=
  (natDegree_C_mul_le _ _).trans (by
    by_cases hp : 0<p
    · have hh :=natDegree_deltaPoly_le_ng twenty_admissible hp
      change (deltaPoly twenty p).natDegree ≤ 20*p-2*p at hh
      have he : 20*p-2*p=18*p :=by omega
      rwa [he] at hh
    · have hp0 : p=0 :=by omega
      subst p
      simpa only [Parameters.n,Nat.mul_zero] using natDegree_deltaPoly_le twenty 0)

theorem twenty_denom_mul_deltaPoly_int_values {p : ℕ} (hp : 1000000000000 ≤ p) (i : ℕ) :
    ∃ m : ℤ, (C (twentyDenomBound p : ℚ) * deltaPoly twenty p).eval (i : ℚ) = m := by
  rw [eval_mul, eval_C, eval_deltaPoly]
  exact twenty_exists_int_denomBound_mul hp i

/-- The integer polynomial `Q_p = (18 p)! · D_p · Δ_p` (and `0` for `p = 0`). -/
noncomputable def twentyMeasureIntPoly (p : ℕ) : ℤ[X] :=
  if hp : 1000000000000 ≤ p then
    Classical.choose (CatalanMeasure.exists_int_poly_factorial_mul
      (C (twentyDenomBound p : ℚ) * deltaPoly twenty p) (natDegree_twenty_denom_mul_deltaPoly_le p)
      (twenty_denom_mul_deltaPoly_int_values hp))
  else 0

theorem twentyMeasureIntPoly_spec {p : ℕ} (hp : 1000000000000 ≤ p) :
    (twentyMeasureIntPoly p).map (Int.castRingHom ℚ) =
        C (((18 * p) ! : ℕ) : ℚ) * (C (twentyDenomBound p : ℚ) * deltaPoly twenty p) ∧
      (twentyMeasureIntPoly p).natDegree ≤ 18 * p := by
  unfold twentyMeasureIntPoly
  rw [dif_pos hp]
  exact Classical.choose_spec (CatalanMeasure.exists_int_poly_factorial_mul
    (C (twentyDenomBound p : ℚ) * deltaPoly twenty p) (natDegree_twenty_denom_mul_deltaPoly_le p)
    (twenty_denom_mul_deltaPoly_int_values hp))

theorem twentyMeasureIntPoly_natDegree_le (p : ℕ) : (twentyMeasureIntPoly p).natDegree ≤ 18 * p := by
  by_cases hp : 1000000000000 ≤ p
  · exact (twentyMeasureIntPoly_spec hp).2
  · unfold twentyMeasureIntPoly
    rw [dif_neg hp]
    simp

theorem aeval_twentyMeasureIntPoly {p : ℕ} (hp : 1000000000000 ≤ p) (x : ℝ) :
    aeval x (twentyMeasureIntPoly p) = ((18 * p) ! : ℝ) * (twentyDenomBound p : ℝ) * aeval x (deltaPoly twenty p) := by
  rw [← aeval_map_algebraMap ℚ x (twentyMeasureIntPoly p), algebraMap_int_eq,
    (twentyMeasureIntPoly_spec hp).1]
  simp only [map_mul, aeval_C, eq_ratCast, Rat.cast_natCast]
  try ring


end
end CatalanMeasure.Parametric
