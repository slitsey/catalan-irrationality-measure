module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPopulationWeights
public import CatalanMeasure.Parametric.PopulationProductPositive
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Filter
open scoped Topology BigOperators
noncomputable section

/-- The actual physical product and actual atom weights, uniformly over all populations. -/
theorem twenty_first_weighted_product_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ) (hpm : p+m=twenty.n N),
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin (18*N)),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective x → Function.Injective s →
      (-(1:ℝ)<∑ i : Fin (p+m),paramCaseField twenty N (Fin.append x y i)) →
      (∀ j,realCoordinateInv (y j)=CatalanMeasure.chebNode (18*N) (a j)) →
      populationOneProduct twenty N hpm x y s*
        (∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|) ≤
      (54000*(N:ℝ))^m*Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m) :=by
  filter_upwards [twenty_first_energy_eventually hδ,eventually_gt_atTop (0:ℕ)]
    with N he hN p m hpm x y s k a hx hx0 hy hs hi hsi hcase hcoord
  have hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx _
    · simp only [Fin.append_right]
      exact ⟨(hy j).1,by linarith only [(hy j).2]⟩
  have hz0 : ∀ c,Fin.append x y c≠0 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx0 _
    · simp only [Fin.append_right]
      exact (hy _).2.ne
  have hM :=populationOneProduct_pos twenty_admissible hN hpm x y s hz hz0 hs hi hsi
  apply twenty_weighted_population_product_bound hN _ δ y k a hcoord hM
  rw [log_populationOneProduct_weighted twenty_admissible hN hpm x y s hz hz0 hs hi hsi]
  exact mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hs hi hsi hcase) (sq_nonneg _)

/-- The actual physical product and actual atom weights, uniformly over all populations. -/
theorem twenty_second_weighted_product_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ) (hpm : p+m=twenty.n N),
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin (18*N)),
      (∀ i,x i ∈ Ioo (-1:ℝ) 1) → (∀ i,x i≠0) →
      (∀ j,y j ∈ Ioo (-1:ℝ) 0) → (∀ j,s j ∈ Ioo (0:ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j,realCoordinateInv (y j)=CatalanMeasure.chebNode (18*N) (a j)) →
      populationTwoProduct twenty N hpm x y s*
        (∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|) ≤
      (54000*(N:ℝ))^m*Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m) :=by
  filter_upwards [twenty_second_energy_eventually hδ,eventually_gt_atTop (0:ℕ)]
    with N he hN p m hpm x y s k a hx hx0 hy hs hi hsi hcoord
  have hz : ∀ c,Fin.append x y c ∈ Ioo (-1:ℝ) 1 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx _
    · simp only [Fin.append_right]
      exact ⟨(hy j).1,by linarith only [(hy j).2]⟩
  have hz0 : ∀ c,Fin.append x y c≠0 :=by
    intro c
    refine Fin.addCases (fun i =>?_) (fun j =>?_) c
    · simpa using hx0 _
    · simp only [Fin.append_right]
      exact (hy _).2.ne
  have hxi : Function.Injective x :=by
    intro i j hij
    have hh :=hi (show Fin.append x y (Fin.castAdd m i)=Fin.append x y (Fin.castAdd m j) by simpa using hij)
    simpa using hh
  have hzi : Function.Injective (fun c : Fin (twenty.n N) =>Fin.append x y (Fin.cast hpm.symm c)) :=
    hi.comp (Fin.cast_injective hpm.symm)
  have hM :=populationTwoProduct_pos twenty_admissible hN hpm x y s hz hz0 hs hxi hsi hzi
  apply twenty_weighted_population_product_bound hN _ δ y k a hcoord hM
  rw [log_populationTwoProduct_weighted twenty_admissible hN hpm x y s hz hz0 hs hxi hsi hzi]
  exact mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hs hi hsi) (sq_nonneg _)

end
end CatalanMeasure.Parametric
