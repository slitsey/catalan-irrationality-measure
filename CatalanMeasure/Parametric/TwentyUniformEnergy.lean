module
public import CatalanMeasure.Parametric.TwentyConcreteEndpoints
public import CatalanMeasure.Parametric.TwentyPhysicalConstants
public import CatalanMeasure.Parametric.WeightedPopulationInterpolation
public import CatalanMeasure.Parametric.TwentyEndpointBudgets
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan TwentyCertified Set Filter
open scoped Topology BigOperators
noncomputable section

/-- Uniform actual weighted energy bound for every missing mass, first to last column. -/
theorem twenty_first_energy_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      (-(1:ℝ)<∑ i : Fin (p+m),paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N ((m:ℝ)/(twenty.n N:ℝ)) x y s ≤
        -twentyDualTarget+Real.log 2/2+(43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ :=by
  filter_upwards [endpoint10_eventually hδ,endpoint11_eventually hδ,eventually_gt_atTop (0:ℕ)]
    with N he0 he1 hN p m hpm x y s hx hx0 hy hs hxi hsi hcase
  let t : ℝ :=(m:ℝ)/(twenty.n N:ℝ)
  let C : ℝ :=populationPhysicalOneConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2
  have hn : (0:ℝ)<twenty.n N :=by exact_mod_cast n_pos twenty_admissible hN
  have ht : 0 ≤ t :=div_nonneg (Nat.cast_nonneg _) hn.le
  have ht1 : t ≤ 1 :=(div_le_one hn).mpr (by exact_mod_cast (show m ≤ twenty.n N by omega))
  have hp : (p:ℝ)/(twenty.n N:ℝ)=1-t :=by
    have hh :=twenty_population_fractions hN hpm
    dsimp only [t]
    linarith only [hh]
  have h0 :=he0 p m hpm x y s hx hx0 hy hs hxi hsi hcase
  have h1 :=he1 p m hpm x y s hx hx0 hy hs hxi hsi hcase
  have hC : C ≤ -(1/5:ℝ)*Real.log 2+(2*t-t^2)*Real.log 2 :=
    twenty_physical_one_constant_le hN hpm
  have hbudget :=twenty_first_endpoint_budget ht
  calc
    weightedPopulationOneValue twenty N t x y s =
        (1-t)*weightedPopulationOneValue twenty N 0 x y s+
        t*weightedPopulationOneValue twenty N 1 x y s :=weightedPopulationOne_affine twenty N t x y s
    _ ≤ (1-t)*(C+twentyNorm10+((p:ℝ)/(twenty.n N:ℝ))*twentyFields10+t*(twentyFixed10)+δ)+
        t*(C+twentyNorm11+((p:ℝ)/(twenty.n N:ℝ))*twentyFields11+t*(twentyFixed11)+δ) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (by linarith only [ht1]))
        (mul_le_mul_of_nonneg_left h1 ht)
    _ = C+(1-t)*(twentyNorm10+(1-t)*twentyFields10+t*(twentyFixed10))+
        t*(twentyNorm11+(1-t)*twentyFields11+t*(twentyFixed11))+δ :=by rw [hp];ring
    _ ≤ -(1/5:ℝ)*Real.log 2+(2*t-t^2)*Real.log 2+
        (1-t)*(twentyNorm10+(1-t)*twentyFields10+t*(twentyFixed10))+
        t*(twentyNorm11+(1-t)*twentyFields11+t*(twentyFixed11))+δ :=by linarith only [hC]
    _ ≤ -twentyDualTarget+Real.log 2/2+(43/10)*t+δ :=by linarith only [hbudget]

/-- Uniform actual weighted energy bound for every missing mass, first to last column. -/
theorem twenty_second_energy_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      weightedPopulationTwoValue twenty N ((m:ℝ)/(twenty.n N:ℝ)) x y s ≤
        -twentyDualTarget+Real.log 2/2+(43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ :=by
  filter_upwards [endpoint20_eventually hδ,endpoint21_eventually hδ,eventually_gt_atTop (0:ℕ)]
    with N he0 he1 hN p m hpm x y s hx hx0 hy hs hxi hsi
  let t : ℝ :=(m:ℝ)/(twenty.n N:ℝ)
  let C : ℝ :=populationPhysicalConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-(1/2:ℝ)*Real.log 2
  have hn : (0:ℝ)<twenty.n N :=by exact_mod_cast n_pos twenty_admissible hN
  have ht : 0 ≤ t :=div_nonneg (Nat.cast_nonneg _) hn.le
  have ht1 : t ≤ 1 :=(div_le_one hn).mpr (by exact_mod_cast (show m ≤ twenty.n N by omega))
  have hp : (p:ℝ)/(twenty.n N:ℝ)=1-t :=by
    have hh :=twenty_population_fractions hN hpm
    dsimp only [t]
    linarith only [hh]
  have h0 :=he0 p m hpm x y s hx hx0 hy hs hxi hsi
  have h1 :=he1 p m hpm x y s hx hx0 hy hs hxi hsi
  have hC : C ≤ -(1/5:ℝ)*Real.log 2+(2*t-t^2)*Real.log 2 :=
    twenty_physical_two_constant_le hN hpm
  have hbudget :=twenty_second_endpoint_budget ht
  calc
    weightedPopulationTwoValue twenty N t x y s =
        (1-t)*weightedPopulationTwoValue twenty N 0 x y s+
        t*weightedPopulationTwoValue twenty N 1 x y s :=weightedPopulationTwo_affine twenty N t x y s
    _ ≤ (1-t)*(C+twentyNorm20+((p:ℝ)/(twenty.n N:ℝ))*twentyFields20+t*(-(1/5:ℝ))+δ)+
        t*(C+twentyNorm21+((p:ℝ)/(twenty.n N:ℝ))*twentyFields21+t*(-(1/5:ℝ))+δ) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (by linarith only [ht1]))
        (mul_le_mul_of_nonneg_left h1 ht)
    _ = C+(1-t)*(twentyNorm20+(1-t)*twentyFields20+t*(-(1/5:ℝ)))+
        t*(twentyNorm21+(1-t)*twentyFields21+t*(-(1/5:ℝ)))+δ :=by rw [hp];ring
    _ ≤ -(1/5:ℝ)*Real.log 2+(2*t-t^2)*Real.log 2+
        (1-t)*(twentyNorm20+(1-t)*twentyFields20+t*(-(1/5:ℝ)))+
        t*(twentyNorm21+(1-t)*twentyFields21+t*(-(1/5:ℝ)))+δ :=by linarith only [hC]
    _ ≤ -twentyDualTarget+Real.log 2/2+(43/10)*t+δ :=by linarith only [hbudget]

end
end CatalanMeasure.Parametric
