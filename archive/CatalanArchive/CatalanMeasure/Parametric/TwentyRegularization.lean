module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCorrectedFields
public import CatalanMeasure.FreePopulationFields
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Filter
open scoped Topology BigOperators
noncomputable section

theorem twenty_reciprocal_three_term_tendsto (A B C D : ℝ) :
    Tendsto (fun N : ℕ =>A/(20*(N:ℝ))+B/(2*(20*(N:ℝ)))+C/(20*(N:ℝ))+D)
      atTop (𝓝 D) :=by
  have hh :=(TwentyCertified.reciprocalScale_tendsto.const_mul (A+B/2+C)).add_const D
  convert hh using 1
  · funext N
    unfold TwentyCertified.reciprocalScale
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · ring

def twentyFirstDampingError (lambda e : ℝ) (pp v : ℕ → ℝ) (N : ℕ) : ℝ :=
  lambda/(20*(N:ℝ))+2*e*(∑' j,|pp j|)+4*e*(∑' j,|v j|)+
    freePopulationRegularizationError (20*(N:ℝ)) e

def twentySecondDampingError (e : ℝ) (pp v : ℕ → ℝ) (N : ℕ) : ℝ :=
  4*e*(∑' j,|pp j|)+4*e*(∑' j,|v j|)+populationRegularizationError (20*(N:ℝ)) e

theorem twentyFirstDampingError_tendsto (lambda e : ℝ) (pp v : ℕ → ℝ) :
    Tendsto (twentyFirstDampingError lambda e pp v) atTop
      (𝓝 (e*(2*(∑' j,|pp j|)+4*(∑' j,|v j|)+14))) :=by
  have hh :=twenty_reciprocal_three_term_tendsto
    ((Real.log 2-2*Real.log (1-realEnergyTau e^2))/2+lambda)
    (Real.log 2-Real.log e) (Real.log 2-2*Real.log e)
    (e*(2*(∑' j,|pp j|)+4*(∑' j,|v j|)+14))
  convert hh using 1
  funext N
  unfold twentyFirstDampingError freePopulationRegularizationError
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem twentySecondDampingError_tendsto (e : ℝ) (pp v : ℕ → ℝ) :
    Tendsto (twentySecondDampingError e pp v) atTop
      (𝓝 (e*(4*(∑' j,|pp j|)+4*(∑' j,|v j|)+16))) :=by
  have hh :=twenty_reciprocal_three_term_tendsto
    (Real.log 2-2*Real.log (1-realEnergyTau e^2))
    (Real.log 2-Real.log e) (Real.log 2-2*Real.log e)
    (e*(4*(∑' j,|pp j|)+4*(∑' j,|v j|)+16))
  convert hh using 1
  funext N
  unfold twentySecondDampingError populationRegularizationError
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem exists_small_population_damping {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0<δ) :
    ∃ e : ℝ,e ∈ Ioo (0:ℝ) (1/8) ∧ e*c<δ :=by
  let e : ℝ :=min (1/16) (δ/(2*(c+1)))
  have he0 : 0<e :=lt_min (by norm_num) (div_pos hδ (by linarith only [hc]))
  have hehi : e ≤ 1/16 :=min_le_left _ _
  have heδ :=min_le_right (1/16:ℝ) (δ/(2*(c+1)))
  have heδ' : e*(2*(c+1)) ≤ δ :=by
    apply (le_div_iff₀ (by linarith only [hc] : (0:ℝ)<2*(c+1))).mp heδ
  refine ⟨e,⟨he0,by linarith only [hehi]⟩,?_⟩
  nlinarith only [heδ',he0,hδ]

/-- Damping is chosen before the scale. The resulting error is uniformly small
    for every configuration and every sufficiently large scale. -/
theorem twentyFirstDampingError_eventually (lambda : ℝ) (pp v : ℕ → ℝ)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ e : ℝ,e ∈ Ioo (0:ℝ) (1/8) ∧
      ∀ᶠ N : ℕ in atTop,twentyFirstDampingError lambda e pp v N ≤ δ :=by
  have hp : 0 ≤ ∑' j,|pp j| :=tsum_nonneg (fun j =>abs_nonneg _)
  have hv : 0 ≤ ∑' j,|v j| :=tsum_nonneg (fun j =>abs_nonneg _)
  obtain ⟨e,he,hec⟩ :=exists_small_population_damping
    (by linarith only [hp,hv] : (0:ℝ) ≤ 2*(∑' j,|pp j|)+4*(∑' j,|v j|)+14) hδ
  refine ⟨e,he,?_⟩
  exact ((tendsto_order.mp (twentyFirstDampingError_tendsto lambda e pp v)).2 δ hec).mono
    (fun _ h =>h.le)

theorem twentySecondDampingError_eventually (pp v : ℕ → ℝ) {δ : ℝ} (hδ : 0<δ) :
    ∃ e : ℝ,e ∈ Ioo (0:ℝ) (1/8) ∧
      ∀ᶠ N : ℕ in atTop,twentySecondDampingError e pp v N ≤ δ :=by
  have hp : 0 ≤ ∑' j,|pp j| :=tsum_nonneg (fun j =>abs_nonneg _)
  have hv : 0 ≤ ∑' j,|v j| :=tsum_nonneg (fun j =>abs_nonneg _)
  obtain ⟨e,he,hec⟩ :=exists_small_population_damping
    (by linarith only [hp,hv] : (0:ℝ) ≤ 4*(∑' j,|pp j|)+4*(∑' j,|v j|)+16) hδ
  refine ⟨e,he,?_⟩
  exact ((tendsto_order.mp (twentySecondDampingError_tendsto e pp v)).2 δ hec).mono
    (fun _ h =>h.le)

end
end CatalanMeasure.Parametric
