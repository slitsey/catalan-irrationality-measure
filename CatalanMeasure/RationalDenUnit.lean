module

public import CatalanMeasure.Parametric.GoodPrimes
public import CatalanMeasure.Parametric.BlockAlgebra
public import CatalanMeasure.Parametric.Polynomial
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeEvenStartingZero

@[expose] public section

/-!
# Denominators of `a / b` and `p * (a / b)` are units modulo `p`

`rat_div_den_unit` and `prime_mul_div_den_unit`, moved unchanged from
`CatalanMeasure.SquareNonvanishing`, so that `GenD.Nonvanishing` no longer imports the
`SquareNonvanishing` / OAI determinant chain.
-/

namespace OAI.InternalCatalan
open Finset Polynomial Matrix
open scoped BigOperators
theorem rat_div_den_unit {p : ℕ} [Fact p.Prime] (a : ℤ) {b : ℕ} (hpb : ¬ p ∣ b) :
    ((((a : ℚ) / b).den : ℕ) : ZMod p) ≠ 0 := by
  intro hzero
  have hden : ((a : ℚ) / b).den ∣ b := by
    have h := Rat.den_dvd a (b : ℤ)
    rw [Rat.divInt_eq_div] at h
    push_cast at h
    exact_mod_cast h
  exact hpb (dvd_trans ((ZMod.natCast_eq_zero_iff _ p).mp hzero) hden)

theorem prime_mul_div_den_unit {p : ℕ} [hpPrime : Fact p.Prime] (a : ℤ)
    {b : ℕ} (hb : 0 < b) (hpb : ¬ p^2 ∣ b) :
    (((p : ℚ) * ((a : ℚ)/b)).den : ZMod p) ≠ 0 := by
  by_cases hd : p ∣ b
  · let c : ℕ := b / p
    have hbc : b = p * c := (Nat.mul_div_cancel' hd).symm
    have hc0 : c ≠ 0 := by intro he; rw [he, mul_zero] at hbc; omega
    have hpc : ¬ p ∣ c := by
      rintro ⟨d, hd⟩
      apply hpb
      refine ⟨d, ?_⟩
      rw [hbc, hd, pow_two]
      ring
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpPrime.out.ne_zero
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hbcq : (b : ℚ) = (p : ℚ) * c := by exact_mod_cast hbc
    have he : (p : ℚ) * ((a : ℚ)/b) = (a : ℚ)/c := by
      rw [hbcq]
      field_simp
    rw [he]
    exact rat_div_den_unit a hpc
  · exact (rational_residue_mul (a := (p : ℚ)) (by simp)
      (rat_div_den_unit a hd)).1

end OAI.InternalCatalan
