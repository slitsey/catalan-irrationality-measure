module
public import CatalanMeasure.Parametric.SecondaryTentParametersFlags
public import CatalanMeasure.Parametric.SecondaryTentRowCancellation
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

def secondaryTentParameterPositiveBetaLinear (p N g boundary δ : ℕ) [Fact p.Prime]
    (β₁ β₂ βE : ZMod p) :
    SecondaryTentParameters (ZMod p) N g boundary →ₗ[ZMod p] (ZMod p)[X] where
  toFun v := X^(4*δ) *
    (C β₁ * secondaryTentCoefficientPolynomial g v.2.1 +
      C β₂ * secondaryTentCoefficientPolynomial g v.2.2.1) +
      C βE * secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1
  map_add' := by
    intro v w
    simp [secondaryTentCoefficientPolynomial, add_mul, mul_add,
      Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro r v
    have h₁ := (secondaryTentCoefficientPolynomialLinear (K := ZMod p) g).map_smul r v.2.1
    have h₂ := (secondaryTentCoefficientPolynomialLinear (K := ZMod p) g).map_smul r v.2.2.1
    have hE := (secondaryTentCoefficientPolynomialLinear (K := ZMod p) (3*N)).map_smul r v.2.2.2.1
    change X^(4*δ) * (C β₁ * secondaryTentCoefficientPolynomial g (r • v.2.1) +
      C β₂ * secondaryTentCoefficientPolynomial g (r • v.2.2.1)) +
      C βE * secondaryTentCoefficientPolynomial (3*N) (r • v.2.2.2.1) = _
    change secondaryTentCoefficientPolynomial g (r • v.2.1) =
      r • secondaryTentCoefficientPolynomial g v.2.1 at h₁
    change secondaryTentCoefficientPolynomial g (r • v.2.2.1) =
      r • secondaryTentCoefficientPolynomial g v.2.2.1 at h₂
    change secondaryTentCoefficientPolynomial (3*N) (r • v.2.2.2.1) =
      r • secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1 at hE
    rw [h₁, h₂, hE]
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply]
    ring

def secondaryTentParameterNegativeBetaLinear (p N g boundary d : ℕ) [Fact p.Prime]
    (β₁ β₂ βE : ZMod p) :
    SecondaryTentParameters (ZMod p) N g boundary →ₗ[ZMod p] (ZMod p)[X] where
  toFun v := C β₁ * secondaryTentCoefficientPolynomial g v.2.1 +
    C β₂ * secondaryTentCoefficientPolynomial g v.2.2.1 +
    X^(4*d) * (C βE * secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)
  map_add' := by
    intro v w
    simp [secondaryTentCoefficientPolynomial, add_mul, mul_add,
      Finset.sum_add_distrib] <;> ring
  map_smul' := by
    intro r v
    simp [secondaryTentCoefficientPolynomial, Polynomial.smul_eq_C_mul,
      Finset.mul_sum, mul_assoc, mul_left_comm] <;> ring

theorem secondaryTent_parameter_positive_beta_degree {p N g boundary δ : ℕ} [Fact p.Prime]
    (hN : 0<N) (hg : 0<g) (hgδ : g+4*δ=3*N)
    (β₁ β₂ βE : ZMod p) (v : SecondaryTentParameters (ZMod p) N g boundary) :
    (secondaryTentParameterPositiveBetaLinear p N g boundary δ β₁ β₂ βE v).natDegree < 3*N := by
  have h₁ := (natDegree_C_mul_le β₁ (secondaryTentCoefficientPolynomial g v.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree hg _)
  have h₂ := (natDegree_C_mul_le β₂ (secondaryTentCoefficientPolynomial g v.2.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree hg _)
  have hE := (natDegree_C_mul_le βE (secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree (by omega : 0<3*N) _)
  have hsum := (natDegree_add_le _ _).trans_lt (max_lt h₁ h₂)
  have hx := natDegree_mul_le (p := (X^(4*δ) : (ZMod p)[X]))
    (q := C β₁ * secondaryTentCoefficientPolynomial g v.2.1+
      C β₂ * secondaryTentCoefficientPolynomial g v.2.2.1)
  rw [natDegree_X_pow] at hx
  have hx' : (X^(4*δ) * (C β₁ * secondaryTentCoefficientPolynomial g v.2.1+
      C β₂ * secondaryTentCoefficientPolynomial g v.2.2.1)).natDegree < 3*N := by omega
  exact (natDegree_add_le _ _).trans_lt (max_lt hx' hE)

theorem secondaryTent_parameter_negative_beta_degree {p N g boundary d : ℕ} [Fact p.Prime]
    (hN : 0<N) (hg : g=3*N+4*d)
    (β₁ β₂ βE : ZMod p) (v : SecondaryTentParameters (ZMod p) N g boundary) :
    (secondaryTentParameterNegativeBetaLinear p N g boundary d β₁ β₂ βE v).natDegree < g := by
  have hg0 : 0<g := by omega
  have h₁ := (natDegree_C_mul_le β₁ (secondaryTentCoefficientPolynomial g v.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree hg0 _)
  have h₂ := (natDegree_C_mul_le β₂ (secondaryTentCoefficientPolynomial g v.2.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree hg0 _)
  have hE := (natDegree_C_mul_le βE (secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)).trans_lt
    (secondaryTent_coefficient_polynomial_degree (by omega : 0<3*N) _)
  have hx := natDegree_mul_le (p := (X^(4*d) : (ZMod p)[X]))
    (q := C βE * secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)
  rw [natDegree_X_pow] at hx
  have hx' : (X^(4*d) * (C βE * secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)).natDegree < g := by omega
  exact (natDegree_add_le _ _).trans_lt
    (max_lt ((natDegree_add_le _ _).trans_lt (max_lt h₁ h₂)) hx')

theorem secondaryTent_parameter_positive_beta_pays {p N g boundary δ a b : ℕ}
    [Fact p.Prime] (hN : 0<N) (hg : 0<g) (hgδ : g+4*δ=3*N) (ha : a=b+4*δ)
    (β₁ β₂ βE : ZMod p) (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hflag : secondaryTentPolynomialWindowLinear 0 (3*N)
      (secondaryTentParameterPositiveBetaLinear p N g boundary δ β₁ β₂ βE v)=0) :
    C β₁ * secondaryTentParameterInputs p N g boundary a b v 1 +
      C β₂ * secondaryTentParameterInputs p N g boundary a b v 2 +
      C βE * secondaryTentParameterInputs p N g boundary a b v 3 = 0 := by
  have hsmall := secondaryTent_polynomial_prefix_eq_zero _
    (secondaryTent_parameter_positive_beta_degree hN hg hgδ β₁ β₂ βE v) hflag
  have hβ : X^(4*δ) * (β₁ • secondaryTentCoefficientPolynomial g v.2.1+
      β₂ • secondaryTentCoefficientPolynomial g v.2.2.1)+
      βE • secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1 = 0 := by
    simpa [secondaryTentParameterPositiveBetaLinear, Polynomial.smul_eq_C_mul] using hsmall
  have hh := secondaryTent_row_positive_beta_flag b (4*δ) β₁ β₂ βE _ _ _ hβ
  simpa [secondaryTentParameterInputs, ha, Polynomial.smul_eq_C_mul] using hh

theorem secondaryTent_parameter_negative_beta_pays {p N g boundary d a b : ℕ}
    [Fact p.Prime] (hN : 0<N) (hg : g=3*N+4*d) (hb : b=a+4*d)
    (β₁ β₂ βE : ZMod p) (v : SecondaryTentParameters (ZMod p) N g boundary)
    (hflag : secondaryTentPolynomialWindowLinear 0 g
      (secondaryTentParameterNegativeBetaLinear p N g boundary d β₁ β₂ βE v)=0) :
    C β₁ * secondaryTentParameterInputs p N g boundary a b v 1 +
      C β₂ * secondaryTentParameterInputs p N g boundary a b v 2 +
      C βE * secondaryTentParameterInputs p N g boundary a b v 3 = 0 := by
  have hsmall := secondaryTent_polynomial_prefix_eq_zero _
    (secondaryTent_parameter_negative_beta_degree hN hg β₁ β₂ βE v) hflag
  have hβ : β₁ • secondaryTentCoefficientPolynomial g v.2.1+
      β₂ • secondaryTentCoefficientPolynomial g v.2.2.1+
      X^(4*d) * (βE • secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1)=0 := by
    simpa [secondaryTentParameterNegativeBetaLinear, Polynomial.smul_eq_C_mul] using hsmall
  have hh := secondaryTent_row_negative_beta_flag a (4*d) β₁ β₂ βE _ _ _ hβ
  simpa [secondaryTentParameterInputs, hb, Polynomial.smul_eq_C_mul] using hh

end
end CatalanMeasure.Parametric
