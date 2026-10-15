module

public import CatalanMeasure.ContentRecycledIntegerLower
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Dividing coefficient content without losing coefficient recycling

All divisibility assumptions here concern coefficients in `ℤ[X]`.
No conclusion is inferred from integer-valued specializations.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial Real
open scoped BigOperators

noncomputable section

/-- Pairwise distinct prime powers assemble a common divisor coefficientwise. -/
theorem primePowerProduct_dvd_coeff (Q : ℤ[X]) (S : Finset ℕ) (e : ℕ → ℕ)
    (hprime : ∀ q ∈ S, q.Prime)
    (hcoeff : ∀ q ∈ S, ∀ i, (q : ℤ) ^ e q ∣ Q.coeff i) (i : ℕ) :
    ((∏ q ∈ S, q ^ e q : ℕ) : ℤ) ∣ Q.coeff i := by
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply IsCoprime.pow
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using (hprime p hp).coprime_iff_not_dvd.mpr (by
      intro hd
      exact hpq ((hprime q hq).eq_one_or_self_of_dvd p hd |>.resolve_left
        (hprime p hp).ne_one))
  · intro q hq
    exact hcoeff q hq i

/-- A prime-power product supported above `2N` is coprime to each recycling prime. -/
theorem primePowerProduct_coprime_of_above {N q : ℕ} (S : Finset ℕ) (e : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (habove : ∀ p ∈ S, 2 * N < p)
    (hq : q.Prime) (hqN : q ≤ 2 * N) :
    Nat.Coprime q (∏ p ∈ S, p ^ e p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  apply Nat.Coprime.pow_right
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  have he := (hprime p hp).eq_one_or_self_of_dvd q hd
  have hqp : q = p := he.resolve_left hq.ne_one
  have := habove p hp
  omega

/-- The integral quotient by a common coefficient divisor (zero if it is not a divisor). -/
def coefficientContentQuotient (Q : ℤ[X]) (c : ℕ) : ℤ[X] := by
  classical
  exact if h : Polynomial.C (c : ℤ) ∣ Q then Classical.choose h else 0

theorem coefficientContentQuotient_spec (Q : ℤ[X]) (c : ℕ)
    (hdiv : ∀ i, (c : ℤ) ∣ Q.coeff i) :
    Q = Polynomial.C (c : ℤ) * coefficientContentQuotient Q c := by
  have h := (Polynomial.C_dvd_iff_dvd_coeff (c : ℤ) Q).mpr hdiv
  unfold coefficientContentQuotient
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem coefficientContentQuotient_natDegree (Q : ℤ[X]) {c : ℕ}
    (hc : 0 < c) (hdiv : ∀ i, (c : ℤ) ∣ Q.coeff i) :
    (coefficientContentQuotient Q c).natDegree = Q.natDegree := by
  have h := congrArg Polynomial.natDegree (coefficientContentQuotient_spec Q c hdiv)
  rw [Polynomial.natDegree_C_mul (by exact_mod_cast hc.ne' : (c : ℤ) ≠ 0)] at h
  exact h.symm

theorem coefficientContentQuotient_aeval (Q : ℤ[X]) {c : ℕ}
    (hc : 0 < c) (hdiv : ∀ i, (c : ℤ) ∣ Q.coeff i) (x : ℝ) :
    aeval x (coefficientContentQuotient Q c) = aeval x Q / c := by
  have h : aeval x Q = (c : ℝ) * aeval x (coefficientContentQuotient Q c) := by
    conv_lhs => rw [coefficientContentQuotient_spec Q c hdiv]
    simp
  rw [h]
  field_simp

theorem coefficientContentQuotient_aeval_ne_zero_iff (Q : ℤ[X]) {c : ℕ}
    (hc : 0 < c) (hdiv : ∀ i, (c : ℤ) ∣ Q.coeff i) (x : ℝ) :
    aeval x (coefficientContentQuotient Q c) ≠ 0 ↔ aeval x Q ≠ 0 := by
  rw [coefficientContentQuotient_aeval Q hc hdiv]
  constructor
  · intro h
    exact (div_ne_zero_iff.mp h).1
  · intro h
    exact div_ne_zero h (by exact_mod_cast hc.ne')

/-- Coprime content preserves the full prime-power divisor of each coefficient. -/
theorem coefficientContentQuotient_coeff_prime_pow_dvd (Q : ℤ[X]) {c q k i : ℕ}
    (hdiv : ∀ j, (c : ℤ) ∣ Q.coeff j) (hcop : Nat.Coprime q c)
    (hcoeff : (q : ℤ) ^ k ∣ Q.coeff i) :
    (q : ℤ) ^ k ∣ (coefficientContentQuotient Q c).coeff i := by
  have hco : IsCoprime ((q : ℤ) ^ k) (c : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa using hcop.pow_left k
  apply hco.dvd_of_dvd_mul_right
  conv at hcoeff => rhs; rw [coefficientContentQuotient_spec Q c hdiv]
  rw [Polynomial.coeff_C_mul] at hcoeff
  rw [mul_comm]
  exact hcoeff

/-- A lower bound on content improves an exponential polynomial estimate additively. -/
theorem coefficientContentQuotient_abs_aeval_le (Q : ℤ[X]) {c : ℕ}
    (hc : 0 < c) (hdiv : ∀ i, (c : ℤ) ∣ Q.coeff i)
    (x A B : ℝ) (hQ : |aeval x Q| ≤ exp (-A)) (hcontent : B ≤ log c) :
    |aeval x (coefficientContentQuotient Q c)| ≤ exp (-(A + B)) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  rw [coefficientContentQuotient_aeval Q hc hdiv, abs_div, abs_of_pos hcR]
  apply (div_le_iff₀ hcR).mpr
  calc
    |aeval x Q| ≤ exp (-A) := hQ
    _ ≤ exp (-(A + B)) * exp (log c) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      linarith
    _ = exp (-(A + B)) * c := by rw [exp_log hcR]

end
end CatalanMeasure.Parametric
