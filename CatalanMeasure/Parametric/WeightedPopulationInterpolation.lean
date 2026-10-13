module
public import CatalanMeasure.Parametric.WeightedPopulationValue
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section

theorem weightedPopulationOne_affine (P : Parameters) (N : ℕ) {p m : ℕ} (a : ℝ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    weightedPopulationOneValue P N a x y s=
      (1-a)*weightedPopulationOneValue P N 0 x y s+
      a*weightedPopulationOneValue P N 1 x y s :=by
  unfold weightedPopulationOneValue freePopulationValueWithFields populationEndpointColumnField
  simp only [zero_mul,add_zero,one_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem weightedPopulationTwo_affine (P : Parameters) (N : ℕ) {p m : ℕ} (a : ℝ)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    weightedPopulationTwoValue P N a x y s=
      (1-a)*weightedPopulationTwoValue P N 0 x y s+
      a*weightedPopulationTwoValue P N 1 x y s :=by
  unfold weightedPopulationTwoValue populationValueWithFields populationEndpointColumnField
  simp only [zero_mul,add_zero,one_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

end
end CatalanMeasure.Parametric
