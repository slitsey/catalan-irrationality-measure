module
public import CatalanMeasure.Parametric.CoefficientContentDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.ZMod
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

/-- Integer evaluations determine coefficient divisibility when the reduction
has degree below the residue-field cardinality. The tail hypothesis matters. -/
theorem coeff_prime_dvd_of_eval_and_tail {p : ℕ} [Fact p.Prime]
    (Q : ℤ[X])
    (htail : ∀ i, p ≤ i → (p : ℤ) ∣ Q.coeff i)
    (heval : ∀ z : ℤ, (p : ℤ) ∣ Q.eval z) :
    ∀ i, (p : ℤ) ∣ Q.coeff i := by
  let S : (ZMod p)[X] := Q.map (Int.castRingHom (ZMod p))
  have hzero : S = 0 := by
    by_cases hS : S = 0
    · exact hS
    have hdegree : S.natDegree < p := by
      by_contra h
      have hz : (Q.coeff S.natDegree : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
          (htail _ (Nat.le_of_not_gt h))
      have hnz : S.coeff S.natDegree ≠ 0 := by
        rw [coeff_natDegree]
        exact leadingCoeff_ne_zero.mpr hS
      apply hnz
      change (Q.map (Int.castRingHom (ZMod p))).coeff S.natDegree = 0
      rw [Polynomial.coeff_map]
      exact hz
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      S Function.injective_id
    · intro z
      have hz : ((Q.eval (z.val : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (heval _)
      calc
        S.eval z = S.eval ((z.val : ℤ) : ZMod p) := by simp
        _ = ((Q.eval (z.val : ℤ) : ℤ) : ZMod p) := by
          exact Polynomial.eval_intCast_map (Int.castRingHom (ZMod p)) Q _
        _ = 0 := hz
    · simpa using hdegree
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hz := congrArg (fun P : (ZMod p)[X] => P.coeff i) hzero
  simpa [S] using hz

/-- A tail already divisible by the full prime power prevents the usual
integer-valued-polynomial obstruction, at every successive residue layer. -/
theorem coeff_prime_pow_dvd_of_eval_and_tail {p : ℕ} [hp : Fact p.Prime]
    (e : ℕ) (Q : ℤ[X])
    (htail : ∀ i, p ≤ i → (p : ℤ) ^ e ∣ Q.coeff i)
    (heval : ∀ z : ℤ, (p : ℤ) ^ e ∣ Q.eval z) :
    ∀ i, (p : ℤ) ^ e ∣ Q.coeff i := by
  induction e generalizing Q with
  | zero => simp
  | succ e ih =>
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpow : (p : ℤ) ∣ (p : ℤ) ^ (e + 1) := by
      rw [pow_succ]
      exact dvd_mul_left _ _
    have hfirst : ∀ i, (p : ℤ) ∣ Q.coeff i :=
      coeff_prime_dvd_of_eval_and_tail Q
        (fun i hi => hpow.trans (htail i hi))
        (fun z => hpow.trans (heval z))
    let R := coefficientContentQuotient Q p
    have hQ : Q = Polynomial.C (p : ℤ) * R :=
      coefficientContentQuotient_spec Q p hfirst
    have hco (i : ℕ) : Q.coeff i = (p : ℤ) * R.coeff i := by
      rw [hQ, coeff_C_mul]
    have hev (z : ℤ) : Q.eval z = (p : ℤ) * R.eval z := by
      rw [hQ, eval_mul, eval_C]
    have htailR : ∀ i, p ≤ i → (p : ℤ) ^ e ∣ R.coeff i := by
      intro i hi
      apply (mul_dvd_mul_iff_left hpz).mp
      rw [← pow_succ', ← hco]
      exact htail i hi
    have hevalR : ∀ z : ℤ, (p : ℤ) ^ e ∣ R.eval z := by
      intro z
      apply (mul_dvd_mul_iff_left hpz).mp
      rw [← pow_succ', ← hev]
      exact heval z
    have hR := ih R htailR hevalR
    intro i
    rw [pow_succ', hco]
    exact mul_dvd_mul_left _ (hR i)

/-- The canonical double-pole coefficient weights supply the needed tail
whenever the desired content exponent is at most `2p`. -/
theorem coeff_prime_pow_dvd_of_weighted_eval {p e : ℕ} [Fact p.Prime]
    (Q : ℤ[X]) (he : e ≤ 2 * p)
    (hweight : ∀ i, (p : ℤ) ^ (2 * i) ∣ Q.coeff i)
    (heval : ∀ z : ℤ, (p : ℤ) ^ e ∣ Q.eval z) :
    ∀ i, (p : ℤ) ^ e ∣ Q.coeff i := by
  apply coeff_prime_pow_dvd_of_eval_and_tail e Q _ heval
  intro i hi
  exact (pow_dvd_pow (p : ℤ) (by omega : e ≤ 2 * i)).trans (hweight i)

end
end CatalanMeasure.Parametric
