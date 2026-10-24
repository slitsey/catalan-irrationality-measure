module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentParametersActualResponse
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentWindowArithmetic
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentMeasureTransfer
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology BigOperators
noncomputable section

theorem secondaryTent_canonical_rank : SecondaryTentCanonicalRankHypothesis := by
  filter_upwards [eventually_ge_atTop (6310886697782126553600:ℕ)] with N hN
  intro p inst hlo hhi
  have hw := secondaryTent_window_data hN hlo hhi
  have hH : twenty.H N<p^2 := by
    rw [twenty_H]
    have hh := hw.source_square
    omega
  by_cases hp : 6*N<p
  · have hp' : p=6*N+(p-6*N) := by omega
    have hδ : 0<p-6*N := by omega
    have hr := secondaryTent_positive_filtered_rank_of_response
      hw.two_unit hw.prime_ne_two hw.seed_unit hw.index_pos hδ hw.g_pos hp'
      hw.prime_odd hw.g_add_four hw.a_add_g hw.b_add_three
      hw.shared_cap_upper hw.lower_endpoint hH (by
        intro v j hjlo hjhi
        exact secondaryTent_positive_actual_raw_response hw.prime_ne_two hw.two_unit
          hw.index_pos hδ hw.g_pos hlo hw.exceptional hp' hw.prime_odd
          hw.g_add_four hw.a_add_g hw.b_add_three hw.shared_cap_upper hw.lower_endpoint
          v j hjlo hjhi)
    omega
  · have hp' : p+(6*N-p)=6*N := by omega
    have hr := secondaryTent_negative_filtered_rank_of_response
      hw.two_unit hw.prime_ne_two hw.seed_unit hw.index_pos hw.g_pos hp'
      hw.prime_odd hw.g_add_four hw.a_add_g hw.b_add_three
      hw.shared_cap_lower hw.shared_cap_upper hH (by
        intro v j hjlo hjhi
        exact secondaryTent_negative_actual_raw_response hw.prime_ne_two hw.two_unit
          hw.index_pos hw.g_pos hlo hw.exceptional hp' hw.prime_odd
          hw.g_add_four hw.a_add_g hw.b_add_three hw.shared_cap_lower hw.shared_cap_upper
          v j hjlo hjhi)
    omega

theorem catalan_irrationalityMeasure_955 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ)^(-(955:ℝ)) < |catalan-(a:ℝ)/b| :=
  catalan_irrationalityMeasure_955_of_canonical_tent_rank secondaryTent_canonical_rank

end
end CatalanMeasure.Parametric
