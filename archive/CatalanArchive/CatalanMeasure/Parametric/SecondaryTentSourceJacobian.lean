module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceSymbol
public import Mathlib.Algebra.Polynomial.Laurent

/-! Finite coefficient form of the constant-term Jacobian calculation for
`t=2z/(1+z²)`. In particular, the negative-power cancellation does not
divide by the exponent, and remains valid when the characteristic divides it. -/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators LaurentPolynomial
noncomputable section

def secondaryTentJacobianNumerator {K : Type*} [CommRing K] (m : ℕ) : K[X] :=
  (1-X^2)*(1+X^2)^(m-1)

theorem secondaryTent_source_jacobian_negative_coeff {K : Type*} [CommRing K]
    {m : ℕ} (hm : 0<m) :
    (secondaryTentJacobianNumerator (K:=K) m).coeff m = 0 := by
  have he : secondaryTentJacobianNumerator (K:=K) m =
      expand K 2 ((1-X)*(1+X)^(m-1)) := by
    simp [secondaryTentJacobianNumerator]
  rw [he, coeff_expand (by decide : 0<2)]
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have hk : 0<k := by omega
    rw [Nat.mul_div_right _ (by decide : 0<2)]
    have hx : (X*(1+X : K[X])^(2*k-1)).coeff k =
        ((1+X : K[X])^(2*k-1)).coeff (k-1) := by
      simpa only [Nat.sub_add_cancel (by omega : 1≤k)] using
        coeff_X_mul ((1+X : K[X])^(2*k-1)) (k-1)
    rw [sub_mul, one_mul, coeff_sub, hx,
      coeff_one_add_X_pow, coeff_one_add_X_pow,
      Nat.choose_symm_of_eq_add (show 2*k-1=k+(k-1) by omega), sub_self]
  · rfl

/-- The polynomial negative sector is exactly the rational substitution
after the factor `z^-m` and scalar `2^-m` have been separated. -/
theorem secondaryTent_source_jacobian_negative_eval {K : Type*} [Field K]
    {m : ℕ} (hm : 0<m) (z : K) (h2 : (2:K)≠0) (hz : z≠0)
    (hq : 1+z^2≠0) :
    (2*z/(1+z^2))^(-(m:ℤ)) * ((1-z^2)/(1+z^2)) =
      (2:K)^(-(m:ℤ))*z^(-(m:ℤ))*
        (secondaryTentJacobianNumerator (K:=K) m).eval z := by
  simp only [secondaryTentJacobianNumerator, eval_mul, eval_sub, eval_add,
    eval_pow, eval_one, eval_X, zpow_neg, zpow_natCast, div_pow, mul_pow]
  rw [pow_sub₀ _ hq (by omega : 1≤m)]
  field_simp

/-- Explicit constant coefficient of a pulled-back Laurent monomial.
Negative exponents use the genuine finite polynomial numerator above;
positive exponents have a positive power of z and a unit denominator. -/
def secondaryTentSubstitutionMonomialCT {K : Type*} [Field K] (n : ℤ) : K :=
  if n=0 then 1 else if n<0 then
    (2:K)^n * (secondaryTentJacobianNumerator (K:=K) n.natAbs).coeff n.natAbs
  else 0

theorem secondaryTent_source_substitution_monomial {K : Type*} [Field K]
    (n : ℤ) : secondaryTentSubstitutionMonomialCT (K:=K) n = if n=0 then 1 else 0 := by
  unfold secondaryTentSubstitutionMonomialCT
  split_ifs with hn hneg
  · rfl
  · rw [secondaryTent_source_jacobian_negative_coeff (Int.natAbs_pos.mpr hn), mul_zero]
  · rfl

/-- Finite linearity gives the exact substitution rule for any Laurent
polynomial in t, including every actual finite source polynomial. -/
def secondaryTentSubstitutionCT {K : Type*} [Field K]
    (F : K[T;T⁻¹]) : K :=
  F.coeff.sum (fun n a => a * secondaryTentSubstitutionMonomialCT (K:=K) n)

theorem secondaryTent_source_substitution_finite {K : Type*} [Field K]
    (F : K[T;T⁻¹]) : secondaryTentSubstitutionCT F = F.coeff 0 := by
  classical
  by_cases h : F.coeff 0=0 <;>
    simp [secondaryTentSubstitutionCT, secondaryTent_source_substitution_monomial,
      Finsupp.sum, h, Finsupp.mem_support_iff]

end
end CatalanMeasure.Parametric
