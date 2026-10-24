module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyRegularization
public import CatalanMeasure.Parametric.WeightedPopulationValue
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Filter
open scoped Topology BigOperators
noncomputable section

theorem population_row_domain {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x≠0) :
    x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1 :=by
  by_cases hneg : x<0
  · exact Or.inl ⟨hx.1.le,hneg⟩
  · exact Or.inr ⟨lt_of_le_of_ne (by linarith only [hneg]) hx0.symm,hx.2⟩

/-- Uniform first-case endpoint control from actual field certificates. -/
theorem twenty_first_endpoint_eventually (a lambda Bx Bs By Kn : ℝ) (pp v : ℕ → ℝ)
    (hlambda : 0 ≤ lambda) (hpp : Summable (fun j =>|pp j|)) (hv : Summable (fun j =>|v j|))
    (hKn : barrierTrialNormSq pp+barrierTrialNormSq v/2 ≤ Kn)
    (hFx : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField twenty N x+lambda*paramCaseField twenty N x-
        2*barrierTrialT pp x-barrierTrialS v x-Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤ Bx+ε)
    (hFy : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ y ∈ Ico (-1:ℝ) 0,
      populationPhysicalOneFixedField twenty N y-populationCommonLog twenty N y/(twenty.n N:ℝ)+
        lambda*paramCaseField twenty N y ≤ By+ε)
    (hFs : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N a s+2*barrierTrialT v s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ Bs+ε)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      (-(1:ℝ)<∑ i : Fin (p+m),paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N a x y s ≤
        populationPhysicalOneConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2+
        Kn+((p:ℝ)/(twenty.n N:ℝ))*(Bx+Bs)+((m:ℝ)/(twenty.n N:ℝ))*By+δ :=by
  let ε : ℝ :=δ/4
  have hε : 0<ε :=by dsimp only [ε];positivity
  obtain ⟨e,he,herr⟩ :=twentyFirstDampingError_eventually lambda pp v hε
  filter_upwards [hFx ε hε,hFy ε hε,hFs ε hε,herr,eventually_gt_atTop (0:ℕ)]
    with N hRow hFixed hColumn hErr hN p m hpm x y s hx hx0 hy hs hxi hsi hcase
  have hn : (0:ℝ)<twenty.n N :=by exact_mod_cast n_pos twenty_admissible hN
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hp : (p:ℝ) ≤ (twenty.n N:ℝ) :=by exact_mod_cast (show p ≤ twenty.n N by omega)
  have hdual :=free_population_fields_dual_bound (constant :=populationPhysicalOneConstant twenty N p)
    hn he hlambda hp
    (populationPhysicalOneFreeField twenty N)
    (fun u =>populationPhysicalOneFixedField twenty N u-populationCommonLog twenty N u/(twenty.n N:ℝ))
    (populationEndpointColumnField twenty N a) (paramCaseField twenty N) x y s hx hs hxi hsi hcase
    pp v hpp hv hKn
    (fun i =>hRow (x i) (population_row_domain (hx i) (hx0 i)))
    (fun j =>hFixed (y j) ⟨(hy j).1.le,(hy j).2⟩) (fun j =>hColumn (s j) (hs j))
  have hbound : weightedPopulationOneValue twenty N a x y s ≤
      populationPhysicalOneConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2+
      Kn+((p:ℝ)/(twenty.n N:ℝ))*(Bx+ε+(Bs+ε))+
      ((m:ℝ)/(twenty.n N:ℝ))*(By+ε)+twentyFirstDampingError lambda e pp v N :=by
    unfold weightedPopulationOneValue
    convert hdual using 1
    unfold twentyFirstDampingError
    rw [hnu]
    ring
  have hm : (0:ℝ) ≤ (m:ℝ)/(twenty.n N:ℝ) :=div_nonneg (Nat.cast_nonneg _) hn.le
  have hp1 : (p:ℝ)/(twenty.n N:ℝ) ≤ 1 :=(div_le_one hn).mpr hp
  have hsum : (p:ℝ)/(twenty.n N:ℝ)+(m:ℝ)/(twenty.n N:ℝ)=1 :=by
    rw [← add_div]
    have hc : (p:ℝ)+(m:ℝ)=(twenty.n N:ℝ) :=by exact_mod_cast hpm
    rw [hc,div_self hn.ne']
  have hsumε :=congrArg (fun t : ℝ =>t*ε) hsum
  have hpε :=mul_le_mul_of_nonneg_right hp1 hε.le
  dsimp only [ε] at hbound hErr hsumε hpε
  nlinarith only [hbound,hErr,hsumε,hpε,hδ]

/-- Uniform second-case endpoint control, retaining the full row population. -/
theorem twenty_second_endpoint_eventually (a Bx Bs By Kn : ℝ) (pp v : ℕ → ℝ)
    (hpp : Summable (fun j =>|pp j|)) (hv : Summable (fun j =>|v j|))
    (hKn : 2*barrierTrialNormSq pp+barrierTrialNormSq v/2 ≤ Kn)
    (hFx : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField twenty N x-4*barrierTrialT pp x-barrierTrialS v x-
        Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤ Bx+ε)
    (hFy : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ y ∈ Ico (-1:ℝ) 0,
      populationPhysicalFixedField twenty N y-populationCommonLog twenty N y/(twenty.n N:ℝ)-
        2*barrierTrialT pp y ≤ By+ε)
    (hFs : ∀ ε : ℝ,0<ε → ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N a s+2*barrierTrialT v s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ Bs+ε)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ),p+m=twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      weightedPopulationTwoValue twenty N a x y s ≤
        populationPhysicalConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-
        (1/2:ℝ)*Real.log 2+Kn+((p:ℝ)/(twenty.n N:ℝ))*(Bx+Bs)+
        ((m:ℝ)/(twenty.n N:ℝ))*By+δ :=by
  let ε : ℝ :=δ/4
  have hε : 0<ε :=by dsimp only [ε];positivity
  obtain ⟨e,he,herr⟩ :=twentySecondDampingError_eventually pp v hε
  filter_upwards [hFx ε hε,hFy ε hε,hFs ε hε,herr,eventually_gt_atTop (0:ℕ)]
    with N hRow hFixed hColumn hErr hN p m hpm x y s hx hx0 hy hs hzi hsi
  have hn : (0:ℝ)<twenty.n N :=by exact_mod_cast n_pos twenty_admissible hN
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have hp : (p:ℝ) ≤ (twenty.n N:ℝ) :=by exact_mod_cast (show p ≤ twenty.n N by omega)
  have hpmR : ((p+m:ℕ):ℝ)=(twenty.n N:ℝ) :=by exact_mod_cast hpm
  have hdual :=population_fields_dual_bound (constant :=populationPhysicalConstant twenty N p)
    hn he hpmR.le (populationPhysicalFreeField twenty N)
    (fun u =>populationPhysicalFixedField twenty N u-populationCommonLog twenty N u/(twenty.n N:ℝ))
    (populationEndpointColumnField twenty N a) x y s hx
    (fun j =>⟨(hy j).1,by linarith only [(hy j).2]⟩) hs hzi hsi pp v hpp hv hKn
    (fun i =>hRow (x i) (population_row_domain (hx i) (hx0 i)))
    (fun j =>hFixed (y j) ⟨(hy j).1.le,(hy j).2⟩) (fun j =>hColumn (s j) (hs j))
  have hbound : weightedPopulationTwoValue twenty N a x y s ≤
      populationPhysicalConstant twenty N p-(3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-
      (1/2:ℝ)*Real.log 2+Kn+((p:ℝ)/(twenty.n N:ℝ))*(Bx+ε+(Bs+ε))+
      ((m:ℝ)/(twenty.n N:ℝ))*(By+ε)+twentySecondDampingError e pp v N :=by
    unfold weightedPopulationTwoValue
    rw [hpmR,div_self hn.ne'] at hdual
    norm_num only [one_pow,mul_one] at hdual
    convert hdual using 1
    unfold twentySecondDampingError
    rw [hnu]
    ring
  have hp1 : (p:ℝ)/(twenty.n N:ℝ) ≤ 1 :=(div_le_one hn).mpr hp
  have hsum : (p:ℝ)/(twenty.n N:ℝ)+(m:ℝ)/(twenty.n N:ℝ)=1 :=by
    rw [← add_div]
    have hc : (p:ℝ)+(m:ℝ)=(twenty.n N:ℝ) :=by exact_mod_cast hpm
    rw [hc,div_self hn.ne']
  have hsumε :=congrArg (fun t : ℝ =>t*ε) hsum
  have hpε :=mul_le_mul_of_nonneg_right hp1 hε.le
  dsimp only [ε] at hbound hErr hsumε hpε
  nlinarith only [hbound,hErr,hsumε,hpε,hδ]

end
end CatalanMeasure.Parametric
