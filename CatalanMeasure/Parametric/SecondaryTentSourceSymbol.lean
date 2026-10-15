module
public import CatalanMeasure.Parametric.SecondaryTentSourceDigit
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The fixed rational source symbol, with denominators cleared

The numerator is derived from the actual signed moment and zeta arrays,
rather than defined from the saved numerical artifact. The evaluation
identity identifies it with the rational seed in equation (T3).
-/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

def secondaryTentSourceNumerator (J : ℕ) : ℚ[X] :=
  (∑ v ∈ Finset.range 6,
    C (momentRatSigned ((v:ℤ)-1) J / 2^v) *
      (1-X^2) * (1+X^2)^v * X^(5-v)) +
  (∑ v ∈ Finset.range 5,
    C ((3/2:ℚ)*zetaRat v J / 2^v) *
      (1+X^2)^(v+1) * X^(5-v))

/-- The actual rational seed, including its signed boundary source. -/
def secondaryTentSourceRationalSeed (J : ℕ) (z : ℚ) : ℚ :=
  ((1-z^2)/(1+z^2)) *
    (∑ v ∈ Finset.range 6,
      momentRatSigned ((v:ℤ)-1) J * (((1+z^2)/(2*z))^v)) +
  (3/2:ℚ) *
    (∑ v ∈ Finset.range 5,
      zetaRat v J * (((1+z^2)/(2*z))^v))

theorem secondaryTent_source_numerator_eval (J : ℕ) (z : ℚ) (hz : z≠0) :
    (secondaryTentSourceNumerator J).eval z =
      z^5*(1+z^2)*secondaryTentSourceRationalSeed J z := by
  have hquad : 1+z^2≠0 := by positivity
  simp only [secondaryTentSourceNumerator, secondaryTentSourceRationalSeed,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_one, eval_zero, eval_X,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Int.reduceSub,
    Int.reduceNeg, Int.cast_ofNat, pow_zero, pow_one, div_one, zero_add]
  field_simp [hz, hquad]
  <;> ring

/-- Integer numerators of the five fixed source seeds, in increasing powers
of z. The common rational denominator is 4608. -/
def secondaryTentSourceNumeratorTable : Matrix (Fin 5) (Fin 13) ℤ :=
  !![156, 737, 1728, 6261, 7500, 9466, 10080, 2810, 3636, -1419, -672, -287, -156;
     256, 60, 2536, -948, 1568, 17784, -4752, 4344, -5600, 4236, -1816, 252, -256;
     -48, 510, -1056, -1530, 4944, 1884, 5184, -1956, 816, -1530, 1632, -258, 48;
     192, -596, -984, 540, -2304, 14328, -4176, -264, -4224, 1692, -1368, 812, -192;
     -352, -999, -424, -3723, 5472, 498, 3792, -2574, -1248, -1419, 856, -231, 352]

set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
/-- This certificate is derived from the repository's actual moment
definitions, including the boundaryPlus value at signed index -1. -/
theorem secondaryTent_source_numerator_certificate (J : Fin 5) :
    C (4608:ℚ) * secondaryTentSourceNumerator J.val =
      ∑ k : Fin 13, C ((secondaryTentSourceNumeratorTable J k : ℤ):ℚ) * X^k.val := by
  apply Polynomial.funext
  intro z
  fin_cases J <;>
    norm_num [secondaryTentSourceNumerator, secondaryTentSourceNumeratorTable,
      momentRatSigned, momentRatNegOne, momentRat, boundaryPlus, boundaryMinus,
      momentScalar, centralCoeff, zetaRat, harmonicRat,
      eval_finsetSum, Finset.sum_range_succ, Fin.sum_univ_succ] <;> ring

theorem secondaryTent_source_moment_denominator_dvd (J : Fin 5) (v : Fin 6) :
    (momentRatSigned ((v.val:ℤ)-1) J.val).den ∣ 4608 := by
  fin_cases J <;> fin_cases v <;> decide +kernel

theorem secondaryTent_source_zeta_denominator_dvd (J v : Fin 5) :
    (zetaRat v.val J.val).den ∣ 4608 := by
  fin_cases J <;> fin_cases v <;> decide +kernel

theorem secondaryTent_source_denominator_dvd_exceptional :
    (4608:ℕ) ∣ 6310886697782126553600 := by norm_num

theorem secondaryTent_source_moment_denominator_unit {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J : Fin 5) (v : Fin 6) :
    (((momentRatSigned ((v.val:ℤ)-1) J.val).den : ℕ) : ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact hp (hd.trans ((secondaryTent_source_moment_denominator_dvd J v).trans
    secondaryTent_source_denominator_dvd_exceptional))

theorem secondaryTent_source_zeta_denominator_unit {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ 6310886697782126553600) (J v : Fin 5) :
    (((zetaRat v.val J.val).den : ℕ) : ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact hp (hd.trans ((secondaryTent_source_zeta_denominator_dvd J v).trans
    secondaryTent_source_denominator_dvd_exceptional))

end
end CatalanMeasure.Parametric
