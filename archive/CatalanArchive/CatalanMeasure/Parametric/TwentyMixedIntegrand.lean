module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyWeightedIntegrand
public import CatalanArchive.CatalanMeasure.Parametric.MixedDegeneracy
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Extend the weighted bound to every integration point, including collisions. -/
theorem twenty_weighted_mixedDouble_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ (p m : ℕ) (hpm : p+m=twenty.n N)
      (E : Fin p → ℕ),Function.Injective E → (∀ i,E i<twenty.n N) →
      ∀ (k : Fin m → ℕ) (a : Fin m → Fin (18*N)) (t s : Fin p → ℝ),
      (∀ i,t i∈Ioo (-1:ℝ) 1) → (∀ i,s i∈Ioo (0:ℝ) 1) →
      |CatalanMeasure.mixedDouble (paramPinRowFun twenty N)
        (CatalanMeasure.chebNode (18*N) ∘ a) (paramPinColFun twenty N E) paramPinKernel t s| *
        (∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|) ≤
        twentySheetPrefactor N*twentyAtomEnergyBound N m δ :=by
  filter_upwards [twenty_weighted_integrand_eventually hδ,eventually_gt_atTop (0:ℕ)]
    with N hbound hN p m hpm E hEi hEn k a t s ht hs
  have hR : 0 ≤ twentySheetPrefactor N*twentyAtomEnergyBound N m δ :=by
    unfold twentySheetPrefactor twentyAtomEnergyBound
    positivity
  by_cases hz : ∃ i,t i=0
  · obtain ⟨i,hi⟩ :=hz
    rw [mixedDouble_eq_zero_of_rowDet (paramRowDet_eq_zero_of_zero twenty_admissible hN hpm _ t hi),
      abs_zero,zero_mul]
    exact hR
  push Not at hz
  by_cases hsi : Function.Injective s
  swap
  · rw [mixedDouble_eq_zero_of_s hsi,abs_zero,zero_mul]
    exact hR
  let x : Fin p → ℝ :=realCoordinate ∘ t
  have hx : ∀ i,x i∈Ioo (-1:ℝ) 1 :=fun i =>realCoordinate_mem (ht i)
  have hx0 : ∀ i,x i≠0 :=by
    intro i hi
    apply hz i
    rw [← realCoordinate_right_inverse (ht i)]
    change realCoordinate (t i)=0 at hi
    rw [hi]
    simp [realCoordinateInv]
  have htx : t=realCoordinateInv ∘ x :=by
    funext i
    exact (realCoordinate_right_inverse (ht i)).symm
  let y : Fin m → ℝ :=fun j =>realCoordinate (CatalanMeasure.chebNode (18*N) (a j))
  have hy : ∀ j,y j∈Ioo (-1:ℝ) 0 :=by
    intro j
    simpa only [y,quadNode] using quadNode_coordinate_mem (18*N) (a j)
  have hcoord : ∀ j,realCoordinateInv (y j)=CatalanMeasure.chebNode (18*N) (a j) :=by
    intro j
    have hh :=CatalanMeasure.chebNode_mem (a j)
    exact realCoordinate_right_inverse ⟨hh.1,by linarith only [hh.2]⟩
  have hty : CatalanMeasure.chebNode (18*N) ∘ a=realCoordinateInv ∘ y :=by
    funext j
    exact (hcoord j).symm
  rw [htx,hty]
  by_cases hi : Function.Injective (Fin.append x y)
  · exact hbound p m hpm E hEi hEn x y s k a hx hx0 hy hs hi hsi hcoord
  have hni : ¬Function.Injective (Fin.append (realCoordinateInv ∘ x) (realCoordinateInv ∘ y)) :=by
    rw [fin_append_comp]
    exact fun hinj =>hi hinj.of_comp
  rw [mixedDouble_eq_zero_of_rowDet (paramRowDet_eq_zero_of_not_injective twenty _ _ hni),
    abs_zero,zero_mul]
  exact hR

end
end CatalanMeasure.Parametric
