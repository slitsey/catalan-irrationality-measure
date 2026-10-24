module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersGeometry
public import CatalanMeasure.Parametric.SecondaryTentFilteredResponse
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentPrimeGrowthWindow
public import CatalanMeasure.Parametric.Polynomial
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- All concrete flag, support, injection and dimension work is closed.
The sole argument left explicit here is the actual raw response identity. -/
theorem secondaryTent_positive_filtered_rank_of_response {p N half δ g a b : ℕ}
    [Fact p.Prime] (h2 : (2:ZMod p)≠0) (hp2 : p≠2)
    (hunit : (3445975817256960:ZMod p)≠0)
    (hN : 0<N) (hδ : 0<δ) (hg : 0<g)
    (hp : p=6*N+δ) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hhi : p≤8*N) (hpN : 2*p≤24*N)
    (hH : twenty.H N<p^2)
    (hraw : ∀ v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentPositiveCosts N p half)
        (secondaryTentPositiveParameterConstraints p N half δ g a b)),
      ∀ j : ℕ, 3*N≤j → j<24*N →
        (∑ r : Fin (20*N), palindromicRatResidue p
          ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
          secondaryTentPositiveActualRowLinear p N half δ g a b v r) =
            (secondaryTentParameterResponsePolynomialLinear p N g (4*δ) v.val).eval (j:ZMod p)) :
    (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank+
      secondaryTentExponent N p≤20*N := by
  have hJ := secondaryTent_positive_actual_row_injective h2 hunit hN hδ hg hp hodd hgp ha hb hhi hpN
  have hr := secondaryTent_rank_of_raw_polynomial_responses (P := twenty) hp2 hH
    0 (by norm_num [palindromicRatResidue]) (secondaryTentPositiveCosts N p half)
    (secondaryTentPositiveParameterConstraints p N half δ g a b)
    (secondaryTentPositiveActualRowLinear p N half δ g a b) hJ (by
      intro v
      refine ⟨secondaryTentParameterResponsePolynomialLinear p N g (4*δ) v.val, ?_, ?_⟩
      · simp only [Parameters.q, twenty, one_mul]
        change (C (secondaryTentParameterResponseScalar p N)*
          secondaryTentResponsePolynomial p N v.val.1).natDegree<N
        exact (natDegree_C_mul_le _ _).trans_lt (secondaryTent_response_polynomial_degree hN _)
      · intro j hjlo hjhi
        exact hraw v j hjlo (by
          simp only [twenty, Parameters.L, Parameters.n, Parameters.b, Parameters.q, one_mul] at hjhi
          omega))
  rw [secondaryTent_parameters_finrank, secondaryTent_positive_count hp hodd hgp hhi] at hr
  rw [secondaryTentExponent_positive_side hp]
  exact hr

theorem secondaryTent_negative_filtered_rank_of_response {p N half g d a b : ℕ}
    [Fact p.Prime] (h2 : (2:ZMod p)≠0) (hp2 : p≠2)
    (hunit : (3445975817256960:ZMod p)≠0)
    (hN : 0<N) (hg : 0<g)
    (hp : p+d=6*N) (hodd : p=2*half+1) (hgp : g+4*p=27*N)
    (ha : a+g=p) (hb : b+3*N=p) (hlo : 8*N+2≤2*p) (hhi : p≤8*N)
    (hH : twenty.H N<p^2)
    (hraw : ∀ v : LinearMap.ker (secondaryTentConstraintMap (secondaryTentNegativeCosts N p half g d)
        (secondaryTentNegativeParameterConstraints p N half g d a b)),
      ∀ j : ℕ, 3*N≤j → j<24*N →
        (∑ r : Fin (20*N), palindromicRatResidue p
          ((p:ℚ)^2*rawEntryRat twenty 0 N r.val j)*
          secondaryTentNegativeActualRowLinear p N half g d a b v r) =
            (secondaryTentParameterResponsePolynomialLinear p N g 0 v.val).eval (j:ZMod p)) :
    (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank+
      secondaryTentExponent N p≤20*N := by
  have hJ := secondaryTent_negative_actual_row_injective h2 hunit hN hg hp hodd hgp ha hb hlo hhi
  have hr := secondaryTent_rank_of_raw_polynomial_responses (P := twenty) hp2 hH
    0 (by norm_num [palindromicRatResidue]) (secondaryTentNegativeCosts N p half g d)
    (secondaryTentNegativeParameterConstraints p N half g d a b)
    (secondaryTentNegativeActualRowLinear p N half g d a b) hJ (by
      intro v
      refine ⟨secondaryTentParameterResponsePolynomialLinear p N g 0 v.val, ?_, ?_⟩
      · simp only [Parameters.q, twenty, one_mul]
        change (C (secondaryTentParameterResponseScalar p N)*
          secondaryTentResponsePolynomial p N v.val.1).natDegree<N
        exact (natDegree_C_mul_le _ _).trans_lt (secondaryTent_response_polynomial_degree hN _)
      · intro j hjlo hjhi
        exact hraw v j hjlo (by
          simp only [twenty, Parameters.L, Parameters.n, Parameters.b, Parameters.q, one_mul] at hjhi
          omega))
  rw [secondaryTent_parameters_finrank, secondaryTent_negative_count hp hodd hgp hhi] at hr
  rw [secondaryTentExponent_negative_side hp]
  exact hr

end
end CatalanMeasure.Parametric
