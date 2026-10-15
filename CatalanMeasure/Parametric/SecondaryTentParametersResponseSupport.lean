module
public import CatalanMeasure.Parametric.SecondaryTentParametersInput
public import CatalanMeasure.Parametric.SecondaryTentSourceModularTrace
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

theorem secondaryTent_parameter_initial_macro_support {p N g boundary a b e : ℕ}
    [Fact p.Prime] (hb : b+3*N=p) (he : e<p) (heN : 3*N≤e)
    (v : SecondaryTentParameters (ZMod p) N g boundary) :
    (secondaryTentParameterInputs p N g boundary a b v 3).coeff (p-1-e)=0 := by
  change (X^b*secondaryTentCoefficientPolynomial (3*N) v.2.2.2.1).coeff (p-1-e)=0
  rw [coeff_X_pow_mul', if_neg (by omega)]

theorem secondaryTent_parameter_boundary_macro_support {p N g δ a b e : ℕ}
    [Fact p.Prime] (hδ : 0<δ) (hp : p=6*N+δ) (he : 3*p+e<24*N)
    (v : SecondaryTentParameters (ZMod p) N g (4*δ)) :
    (secondaryTentParameterInputs p N g (4*δ) a b v 4).coeff (p-1-e)=0 := by
  change (secondaryTentCoefficientPolynomial (4*δ) v.2.2.2.2).coeff (p-1-e)=0
  apply coeff_eq_zero_of_natDegree_lt
  have hh := secondaryTent_coefficient_polynomial_degree (by omega : 0<4*δ) v.2.2.2.2
  omega

theorem secondaryTent_parameter_zero_boundary {p N g a b : ℕ} [Fact p.Prime]
    (v : SecondaryTentParameters (ZMod p) N g 0) :
    secondaryTentParameterInputs p N g 0 a b v 4=0 := by
  simp [secondaryTentParameterInputs, secondaryTentCoefficientPolynomial]

/-- Exact bulk fixed-source response, using only physical column
availability. This also explains why the boundary seed is harmless. -/
theorem secondaryTent_parameter_positive_macro_response {p N g δ a b e : ℕ}
    [Fact p.Prime] (hNp : N≤p) (hδ : 0<δ) (hp : p=6*N+δ)
    (hb : b+3*N=p) (he : e<p) (J : Fin 4)
    (hlo : 3*N≤J.val*p+e) (hhi : J.val*p+e<24*N)
    (v : SecondaryTentParameters (ZMod p) N g (4*δ)) :
    (∑ i : Fin 5, (secondaryTentSourceFixedResponseInteger J i:ZMod p)*
      (secondaryTentParameterInputs p N g (4*δ) a b v i).coeff (p-1-e)) =
      (747824613120:ZMod p)*(secondaryTentResponsePolynomial p N v.1).eval (e:ZMod p) := by
  have hF : (secondaryTentParameterInputs p N g (4*δ) a b v 0).coeff (p-1-e)=
      (secondaryTentResponsePolynomial p N v.1).eval (e:ZMod p) :=
    secondaryTent_response_input_coeff hNp v.1 he
  fin_cases J
  · have hE := secondaryTent_parameter_initial_macro_support (a := a) hb he (by simpa using hlo) v
    simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF, hE]
  · simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF]
  · simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF]
  · have hB := secondaryTent_parameter_boundary_macro_support (a := a) (b := b) hδ hp (by simpa using hhi) v
    simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF, hB]

theorem secondaryTent_parameter_negative_macro_response {p N g a b e : ℕ}
    [Fact p.Prime] (hNp : N≤p) (hb : b+3*N=p) (he : e<p) (J : Fin 4)
    (hlo : 3*N≤J.val*p+e) (v : SecondaryTentParameters (ZMod p) N g 0) :
    (∑ i : Fin 5, (secondaryTentSourceFixedResponseInteger J i:ZMod p)*
      (secondaryTentParameterInputs p N g 0 a b v i).coeff (p-1-e)) =
      (747824613120:ZMod p)*(secondaryTentResponsePolynomial p N v.1).eval (e:ZMod p) := by
  have hF : (secondaryTentParameterInputs p N g 0 a b v 0).coeff (p-1-e)=
      (secondaryTentResponsePolynomial p N v.1).eval (e:ZMod p) :=
    secondaryTent_response_input_coeff hNp v.1 he
  have hB : (secondaryTentParameterInputs p N g 0 a b v 4).coeff (p-1-e)=0 := by
    rw [secondaryTent_parameter_zero_boundary]
    simp
  fin_cases J
  · have hE := secondaryTent_parameter_initial_macro_support (a := a) hb he (by simpa using hlo) v
    simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF, hE]
  · simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF]
  · simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF]
  · simp [secondaryTentSourceFixedResponseInteger, Fin.sum_univ_succ, hF, hB]

end
end CatalanMeasure.Parametric
