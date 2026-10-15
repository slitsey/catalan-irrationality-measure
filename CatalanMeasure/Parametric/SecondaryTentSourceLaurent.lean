module
public import CatalanMeasure.Parametric.SecondaryTentSourceJacobian

/-! The actual scaled source as a literal finite Laurent polynomial in t,
with its finite Jacobian substitution, rather than a model response. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators LaurentPolynomial
noncomputable section

/-- Polynomial evaluation injectivity extends to finite Laurent polynomials
by clearing a single power of the unit variable. -/
theorem secondaryTent_source_laurent_eval_injective_of_polynomial
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (x : Lˣ)
    (hpoly : Function.Injective (Polynomial.eval₂RingHom f (x:L))) :
    Function.Injective (LaurentPolynomial.eval₂ f x) := by
  have hzero (F : K[T;T⁻¹]) (hF : LaurentPolynomial.eval₂ f x F=0) : F=0 := by
    induction F using LaurentPolynomial.induction_on_mul_T with
    | mul_T I n =>
      have hunit : LaurentPolynomial.eval₂ f x
          (LaurentPolynomial.T (-(n:ℤ)))≠0 := by
        rw [LaurentPolynomial.eval₂_T_neg_n]
        exact pow_ne_zero n (Units.ne_zero (x⁻¹))
      rw [map_mul, LaurentPolynomial.eval₂_toLaurent] at hF
      have hI : I=0 := by
        apply hpoly
        simpa using (mul_eq_zero.mp hF).resolve_right hunit
      simp [hI]
  intro F G hFG
  apply sub_eq_zero.mp
  apply hzero
  simp only [map_sub, hFG, sub_self]

theorem secondaryTent_source_laurent_eval_injective {p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) : Function.Injective
      (LaurentPolynomial.eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
        (Units.mk0 (palindromicRatT p) (palindromicRat_T_ne_zero hp2))) :=
  secondaryTent_source_laurent_eval_injective_of_polynomial _ _
    (palindromicRatT_eval₂RingHom_injective hp2)

theorem secondaryTent_source_toLaurent_coeff_nat {K : Type*} [CommRing K]
    (I : K[X]) (n : ℕ) : I.toLaurent.coeff (n:ℤ)=I.coeff n := by
  change (I.toFinsupp.coeff.mapDomain (fun a:ℕ => (a:ℤ))) (n:ℤ)=I.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

theorem secondaryTent_source_toLaurent_shift_ct {K : Type*} [CommRing K]
    (I : K[X]) (n : ℕ) :
    (I.toLaurent*LaurentPolynomial.T (-(n:ℤ))).coeff 0=I.coeff n := by
  simpa only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply,
    sub_neg_eq_add, zero_add, neg_neg, mul_one] using secondaryTent_source_toLaurent_coeff_nat I n

/-- The x-coordinate form of the same finite Jacobian: since
`s=-x*s0`, its constant term extracts minus the x^-1 coefficient. -/
def secondaryTentSourceXCT {K : Type*} [Field K] (L : K[T;T⁻¹]) : K :=
  -secondaryTentSubstitutionCT
    (LaurentPolynomial.invert L*LaurentPolynomial.T (-1))

theorem secondaryTent_source_x_jacobian {K : Type*} [Field K]
    (L : K[T;T⁻¹]) : secondaryTentSourceXCT L = -L.coeff (-1) := by
  simp only [secondaryTentSourceXCT, secondaryTent_source_substitution_finite,
    LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply,
    sub_neg_eq_add, zero_add, neg_neg, mul_one, LaurentPolynomial.invert_apply]

def secondaryTentSourceLaurentRaw (P : Parameters) (p N r j : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] :=
  (X*oddPrimeWeight p*((rowP P N r).map (Int.castRingHom (ZMod p))) *
    (secondaryTentSourceMoment p (j/p))^p).toLaurent *
      LaurentPolynomial.T (-((5*p+j%p:ℕ):ℤ)) -
  (3/2:ZMod p) •
    ((((rowD P N r).map (Int.castRingHom (ZMod p))) *
      (secondaryTentSourceZeta p (j/p))^p).toLaurent *
        LaurentPolynomial.T (-((4*p+j%p:ℕ):ℤ)))

theorem secondaryTent_source_twenty_laurent_substitution {p N r j : ℕ}
    [Fact p.Prime] (hN : 0<N) (hwindow : 52*N<9*p) (hj : j<24*N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty z N r j) =
      secondaryTentSubstitutionCT (secondaryTentSourceLaurentRaw twenty p N r j) := by
  rw [secondaryTent_source_substitution_finite]
  simpa only [secondaryTentSourceLaurentRaw, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_smul, Finsupp.sub_apply, Finsupp.smul_apply,
    smul_eq_mul, secondaryTent_source_toLaurent_shift_ct] using
      secondaryTent_source_twenty_raw_entry hN hwindow hj z hzp

end
end CatalanMeasure.Parametric
