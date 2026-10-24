module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentSourceRawSectors

/-! Ordinary source numerators reflected into finite Laurent sources in t. -/
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators LaurentPolynomial
noncomputable section

def secondaryTentSourceReflected {K : Type*} [CommRing K] (S : K[X]) (m : ℕ) :
    K[T;T⁻¹] := LaurentPolynomial.invert S.toLaurent*LaurentPolynomial.T (m:ℤ)

theorem secondaryTent_source_reflected_coeff {K : Type*} [CommRing K]
    (S : K[X]) (m : ℕ) : (secondaryTentSourceReflected S m).coeff 0=S.coeff m := by
  simp only [secondaryTentSourceReflected, LaurentPolynomial.T,
    AddMonoidAlgebra.coeff_mul_single_apply, zero_sub, mul_one,
    LaurentPolynomial.invert_apply, zero_add, neg_neg]
  exact secondaryTent_source_toLaurent_coeff_nat S m

theorem secondaryTent_source_invert_polynomial_eval {K L : Type*}
    [CommRing K] [Field L] (f : K →+* L) (t : Lˣ) (S : K[X]) :
    LaurentPolynomial.eval₂ f t (LaurentPolynomial.invert S.toLaurent) =
      S.eval₂ f (t⁻¹:Lˣ) := by
  induction S using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ, eval₂_add]
  | monomial n a =>
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T_neg_n, eval₂_monomial]

theorem secondaryTent_source_reflected_eval {K L : Type*}
    [CommRing K] [Field L] (f : K →+* L) (t : Lˣ) (S : K[X]) (m : ℕ) :
    LaurentPolynomial.eval₂ f t (secondaryTentSourceReflected S m) =
      S.eval₂ f (t⁻¹:Lˣ)*(t:L)^m := by
  rw [secondaryTentSourceReflected, map_mul, secondaryTent_source_invert_polynomial_eval,
    LaurentPolynomial.eval₂_T_n]

end
end CatalanMeasure.Parametric
