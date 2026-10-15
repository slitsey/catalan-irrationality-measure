module
public import CatalanMeasure.Parametric.SecondaryTentReconstruction
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Explicit independent differential seeds for the secondary tent

Columns are the five actual human-proof differential seeds, multiplied
by the common denominator 747824613120. Rows are the coefficients of
dz/z, dz, z dz, dz/(z-1), dz/(1+z²), z dz/(1+z²), dz/z².
The integer left inverse proves independence over every field in which
3445975817256960 is nonzero, including the required prime fields.
-/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Matrix
open scoped BigOperators
noncomputable section

def secondaryTentSeedCoefficients : Matrix (Fin 7) (Fin 5) ℤ :=
  !![22793908405248, -1808511970683, -955889757237, 7809343308288, 171366094080;
    -10994814904320, 1019297963710, 284223856930, -3202250388480, -332702277120;
    -4579798984704, 424690209574, 124015834426, -1067286979584, -44350502400;
    -65688680346624, 6028866125879, 1515140778041, -20441924135424, 0;
    0, 747824613120, 0, 0, 0;
    0, 0, 747824613120, 0, 0;
    0, 0, 0, 0, 747824613120]

def secondaryTentSeedLeftInverse : Matrix (Fin 5) (Fin 7) ℤ :=
  !![-984, 3768, -3336, -792, 764, -532, 1704;
    0, 0, 0, 0, 4608, 0, 0;
    0, 0, 0, 0, 0, 4608, 0;
    1960, -3704, 7976, 744, -739, 1083, -1624;
    0, 0, 0, 0, 0, 0, 4608]

theorem secondaryTent_seed_integer_left_inverse :
    secondaryTentSeedLeftInverse * secondaryTentSeedCoefficients =
      (3445975817256960 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondaryTentSeedLeftInverse, secondaryTentSeedCoefficients,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem secondaryTent_seed_field_left_inverse {K : Type*} [Field K] :
    secondaryTentSeedLeftInverse.map (Int.castRingHom K) *
        secondaryTentSeedCoefficients.map (Int.castRingHom K) =
      (3445975817256960 : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
  rw [← Matrix.map_mul, secondaryTent_seed_integer_left_inverse]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> norm_num

theorem secondaryTent_seed_coefficients_injective {K : Type*} [Field K]
    (hunit : (3445975817256960 : K) ≠ 0) :
    Function.Injective
      (secondaryTentSeedCoefficients.map (Int.castRingHom K)).mulVec := by
  intro u v huv
  have hh := congrArg
    (secondaryTentSeedLeftInverse.map (Int.castRingHom K)).mulVec huv
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    secondaryTent_seed_field_left_inverse] at hh
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at hh
  funext i
  exact mul_left_cancel₀ hunit (congrFun hh i)

/-- The fixed exceptional integer in the human proof also pays this concrete
integer left-inverse certificate; no new exceptional primes are introduced. -/
theorem secondaryTent_seed_certificate_dvd_exceptional :
    (3445975817256960 : ℕ) ∣ 6310886697782126553600 ^ 2 := by
  norm_num

theorem secondaryTent_seed_coefficients_injective_zmod {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ 6310886697782126553600) :
    Function.Injective
      (secondaryTentSeedCoefficients.map (Int.castRingHom (ZMod p))).mulVec := by
  apply secondaryTent_seed_coefficients_injective
  intro hz
  have hd : p ∣ 3445975817256960 := (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact hp ((Fact.out : p.Prime).dvd_of_dvd_pow
    (hd.trans secondaryTent_seed_certificate_dvd_exceptional))

end
end CatalanMeasure.Parametric
