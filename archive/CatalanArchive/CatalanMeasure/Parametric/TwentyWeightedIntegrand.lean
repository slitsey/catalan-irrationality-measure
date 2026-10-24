module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyWeightedMajorants
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Finset Filter
open scoped Topology BigOperators
noncomputable section

def twentySheetPrefactor (N : ℕ) : ℝ :=
  (3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^((twenty.n N:ℝ)/2)+
    (1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N)

def twentyAtomEnergyBound (N m : ℕ) (δ : ℝ) : ℝ :=
  (54000*(N:ℝ))^m*Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m)

/-- The actual mixed integrand and atom weights obey one bound in both sheet cases. -/
theorem twenty_weighted_integrand_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ) (hpm : p+m=twenty.n N)
      (E : Fin p → ℕ),Function.Injective E → (∀ i,E i<twenty.n N) →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin (18*N)),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j,realCoordinateInv (y j)=CatalanMeasure.chebNode (18*N) (a j)) →
      |CatalanMeasure.mixedDouble (paramPinRowFun twenty N) (realCoordinateInv ∘ y)
        (paramPinColFun twenty N E) paramPinKernel (realCoordinateInv ∘ x) s| *
        (∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|) ≤
        twentySheetPrefactor N*twentyAtomEnergyBound N m δ :=by
  filter_upwards [twenty_first_weighted_product_eventually hδ,
      twenty_second_weighted_product_eventually hδ,eventually_gt_atTop (2:ℕ)]
    with N he1 he2 hN3 p m hpm E hEi hEn x y s k a hx hx0 hy hs hi hsi hcoord
  have hN : 0<N :=by omega
  let z : Fin (twenty.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  let W : ℝ :=∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|
  have hW : 0 ≤ W :=prod_nonneg (fun j _ =>abs_nonneg _)
  have hR : 0 ≤ twentyAtomEnergyBound N m δ :=by unfold twentyAtomEnergyBound;positivity
  have hxi : Function.Injective x :=by
    intro i j hij
    have hh :=hi (show Fin.append x y (Fin.castAdd m i)=Fin.append x y (Fin.castAdd m j) by simpa using hij)
    simpa using hh
  have hzi : Function.Injective z :=hi.comp (Fin.cast_injective hpm.symm)
  have hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx i
    · simp only [Fin.append_right]
      exact ⟨(hy j).1,by linarith only [(hy j).2]⟩
  have hz0 : ∀ c,Fin.append x y c≠0 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx0 i
    · simp only [Fin.append_right]
      exact (hy j).2.ne
  have hsum : (∑ c : Fin (twenty.n N),paramCaseField twenty N (z c))=
      ∑ c : Fin (p+m),paramCaseField twenty N (Fin.append x y c) :=
    sum_fin_cast hpm (fun c =>paramCaseField twenty N (Fin.append x y c))
  by_cases hcase : -(1:ℝ)<∑ c : Fin (p+m),paramCaseField twenty N (Fin.append x y c)
  · have hbase :=param_mixedDouble_population_one twenty_admissible hN hpm E hEi hEn x y s hz hz0 hs
    have hp :=he1 p m hpm x y s k a hx hx0 hy hs hxi hsi hcase hcoord
    calc
      _ ≤ ((3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^((twenty.n N:ℝ)/2))*
          (populationOneProduct twenty N hpm x y s*W) :=by
        have hh :=mul_le_mul_of_nonneg_right hbase hW
        convert hh using 1 <;> ring
      _ ≤ ((3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^((twenty.n N:ℝ)/2))*
          twentyAtomEnergyBound N m δ :=mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ :=by
        apply mul_le_mul_of_nonneg_right _ hR
        unfold twentySheetPrefactor
        have hh : 0 ≤ (1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N) :=by positivity
        linarith only [hh]
  · have hcase' : (∑ c,paramCaseField twenty N (z c)) ≤ -(1:ℝ) :=by
      rw [hsum]
      exact le_of_not_gt hcase
    have hsecond :=paramCaseField_second_case twenty_admissible hN z hcase'
    have hn48 : 48 ≤ twenty.n N :=by simp only [Parameters.n,twenty];omega
    have hD : 0<twenty.n N-1-2*twenty.g N :=by simp only [Parameters.n,Parameters.g,twenty];omega
    have hbase :=param_mixedDouble_population_two twenty_admissible hN hpm E hEi hEn x y s hz hz0 hs
      hzi hn48 hD hsecond
    have hp :=he2 p m hpm x y s k a hx hx0 hy hs hi hsi hcoord
    calc
      _ ≤ (1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N)*
          (populationTwoProduct twenty N hpm x y s*W) :=by
        have hh :=mul_le_mul_of_nonneg_right hbase hW
        convert hh using 1 <;> ring
      _ ≤ (1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N)*
          twentyAtomEnergyBound N m δ :=mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ :=by
        apply mul_le_mul_of_nonneg_right _ hR
        unfold twentySheetPrefactor
        have hh : 0 ≤ (3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^((twenty.n N:ℝ)/2) :=by positivity
        linarith only [hh]

end
end CatalanMeasure.Parametric
