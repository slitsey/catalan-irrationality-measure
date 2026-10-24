module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPhysicalCertifiedFields
public import CatalanArchive.CatalanMeasure.Parametric.TwentyEndpointControl
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCertified
open OAI.InternalCatalan Set Filter
open scoped Topology BigOperators
noncomputable section

theorem endpoint10_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      (-(1:ℝ)<∑ i : Fin (p+m),paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N 0 x y s ≤
        populationPhysicalOneConstant twenty N p-
        (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2+
        twentyNorm10+((p:ℝ)/(twenty.n N:ℝ))*twentyFields10+
        ((m:ℝ)/(twenty.n N:ℝ))*(twentyFixed10)+δ :=by
  have hh :=twenty_first_endpoint_eventually 0 (lambda10:ℝ)
    (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ) (CatalanMeasure.TwentyTrial.K1A0.MY:ℝ)
    (twentyFixed10) twentyNorm10 p10 v10
    (by norm_num [lambda10]) p10_summable v10_summable
    (by simpa only [one_mul] using norm10_bound)
    (fun ε hε =>physical_row10_eventually hε)
    (fun ε hε =>by
      filter_upwards [fixed10_corrected_eventually hε] with N hc y hy
      linarith only [hc y hy])
    (fun ε hε =>physical_column10_eventually hε) hδ
  rw [fieldSum10] at hh
  exact hh

theorem endpoint11_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      (-(1:ℝ)<∑ i : Fin (p+m),paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N 1 x y s ≤
        populationPhysicalOneConstant twenty N p-
        (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2+
        twentyNorm11+((p:ℝ)/(twenty.n N:ℝ))*twentyFields11+
        ((m:ℝ)/(twenty.n N:ℝ))*(twentyFixed11)+δ :=by
  have hh :=twenty_first_endpoint_eventually 1 (lambda11:ℝ)
    (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ) (CatalanMeasure.TwentyTrial.K1A1.MY:ℝ)
    (twentyFixed11) twentyNorm11 p11 v11
    (by norm_num [lambda11]) p11_summable v11_summable
    (by simpa only [one_mul] using norm11_bound)
    (fun ε hε =>physical_row11_eventually hε)
    (fun ε hε =>by
      filter_upwards [fixed11_corrected_eventually hε] with N hc y hy
      linarith only [hc y hy])
    (fun ε hε =>physical_column11_eventually hε) hδ
  rw [fieldSum11] at hh
  exact hh

theorem endpoint20_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      weightedPopulationTwoValue twenty N 0 x y s ≤
        populationPhysicalConstant twenty N p-
        (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-(1/2:ℝ)*Real.log 2+
        twentyNorm20+((p:ℝ)/(twenty.n N:ℝ))*twentyFields20+
        ((m:ℝ)/(twenty.n N:ℝ))*(-(1/5:ℝ))+δ :=by
  have hh :=twenty_second_endpoint_eventually 0
    (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ) (CatalanMeasure.TwentyTrial.K2A0.MY:ℝ)
    (-(1/5:ℝ)) twentyNorm20 p20 v20
    p20_summable v20_summable norm20_bound
    (fun ε hε =>physical_row20_eventually hε)
    (fun ε hε =>by
      filter_upwards [fixed20_corrected_eventually hε] with N hc y hy
      linarith only [hc y hy])
    (fun ε hε =>physical_column20_eventually hε) hδ
  rw [fieldSum20] at hh
  exact hh

theorem endpoint21_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      weightedPopulationTwoValue twenty N 1 x y s ≤
        populationPhysicalConstant twenty N p-
        (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-(1/2:ℝ)*Real.log 2+
        twentyNorm21+((p:ℝ)/(twenty.n N:ℝ))*twentyFields21+
        ((m:ℝ)/(twenty.n N:ℝ))*(-(1/5:ℝ))+δ :=by
  have hh :=twenty_second_endpoint_eventually 1
    (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ) (CatalanMeasure.TwentyTrial.K2A1.MY:ℝ)
    (-(1/5:ℝ)) twentyNorm21 p21 v21
    p21_summable v21_summable norm21_bound
    (fun ε hε =>physical_row21_eventually hε)
    (fun ε hε =>by
      filter_upwards [fixed21_corrected_eventually hε] with N hc y hy
      linarith only [hc y hy])
    (fun ε hε =>physical_column21_eventually hε) hδ
  rw [fieldSum21] at hh
  exact hh

end
end CatalanMeasure.Parametric.TwentyCertified
