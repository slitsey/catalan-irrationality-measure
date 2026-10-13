module
public import CatalanMeasure.Parametric.TwentyMixedIntegrand
public import CatalanMeasure.WeightedMixedAndreief
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

open Set Finset MeasureTheory Matrix Filter

def twentyRealBaseMatrix (N : ℕ) : Matrix (Fin (twenty.n N)) (Fin (twenty.n N)) ℝ :=
  fun r k =>realEntry twenty N r.val k.val

def twentyAtomVectors (N : ℕ) : Fin (twenty.n N) → Fin (18*N) → ℝ :=
  fun r a =>realRowAmplitude twenty N r.val (CatalanMeasure.chebNode (18*N) a)

def twentyAtomWeights (N : ℕ) : Fin (18*N) → Fin (twenty.n N) → ℝ :=
  fun a k =>restrictedWeight twenty N k.val (CatalanMeasure.chebNode (18*N)) a

def twentyAtomColumnCost (N : ℕ) : ℝ :=54000*(N:ℝ)*Real.exp (119*(N:ℝ))

def twentyAtomBaseBound (N : ℕ) (δ : ℝ) : ℝ :=
  (2:ℝ)^(twenty.n N)*twentySheetPrefactor N*
    Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ))

theorem twenty_weighted_atomMatrix_det_eventually {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ N : ℕ in atTop,∀ f : Fin (twenty.n N) → Option (Fin (18*N)),
      (∏ k,(f k).elim 1 (fun a =>|twentyAtomWeights N a k|)) *
        |(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyAtomVectors N) f).det| ≤
      twentyAtomBaseBound N δ*∏ k,(f k).elim 1 (fun _ =>twentyAtomColumnCost N) :=by
  filter_upwards [twenty_weighted_mixedDouble_eventually hδ] with N hbound f
  classical
  let P : Fin (twenty.n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // P k} + Fintype.card {k // ¬ P k} = twenty.n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le P
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // P k} with hp
  set m := Fintype.card {k // ¬ P k} with hm
  let e : Fin (p + m) ≃ Fin (twenty.n N) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin {k // P k}).symm
      (Fintype.equivFin {k // ¬ P k}).symm)).trans (Equiv.sumCompl P)
  have he1 : ∀ i : Fin p, f (e (Fin.castAdd m i)) = none := by
    intro i
    have h : e (Fin.castAdd m i) = ((Fintype.equivFin {k // P k}).symm i).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // P k}).symm i).property
  have he2 : ∀ j : Fin m, f (e (Fin.natAdd p j)) ≠ none := by
    intro j
    have h : e (Fin.natAdd p j) = ((Fintype.equivFin {k // ¬ P k}).symm j).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // ¬ P k}).symm j).property
  let E : Fin p → ℕ := fun i => (e (Fin.castAdd m i)).val
  have hE : Function.Injective E := by
    intro i i' hii
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hii))
  have hEn : ∀ i, E i < twenty.n N := fun i => (e (Fin.castAdd m i)).isLt
  let av : Fin m → Fin (18*N) :=fun j =>Classical.choose (Option.ne_none_iff_exists'.mp (he2 j))
  have hav (j : Fin m) : f (e (Fin.natAdd p j))=some (av j) :=
    Classical.choose_spec (Option.ne_none_iff_exists'.mp (he2 j))
  let kv : Fin m → ℕ :=fun j =>(e (Fin.natAdd p j)).val
  let yv : Fin m → ℝ :=fun j =>realCoordinate (CatalanMeasure.chebNode (18*N) (av j))
  have hyv : ∀ j,yv j ∈ Ioo (-1:ℝ) 0 :=by
    intro j
    simpa only [yv,quadNode] using quadNode_coordinate_mem (18*N) (av j)
  have hcoord (j : Fin m) : realCoordinateInv (yv j)=CatalanMeasure.chebNode (18*N) (av j) :=by
    have hh :=CatalanMeasure.chebNode_mem (av j)
    exact realCoordinate_right_inverse ⟨hh.1,by linarith only [hh.2]⟩
  have hmat : (CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyAtomVectors N) f).submatrix
      (finCongr hpm) e =
      CatalanMeasure.mixedMatrix realPlaceMeasure (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))
        (paramPinRowFun twenty N) (realCoordinateInv ∘ yv) (paramPinColFun twenty N E) paramPinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_left, twentyRealBaseMatrix]
      rw [realEntry_eq_realPlace_product twenty]
      congr 1
      funext z
      simp only [paramPinRowFun, paramPinColFun, paramPinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (he2 j)
      have hτ := quadNode_mem (18*N) a
      simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, ha,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_right, twentyAtomVectors, paramPinRowFun,
        Function.comp_apply, yv, finCongr_apply, Fin.val_cast]
      have heq : a=av j :=by have hh :=hav j;rw [ha] at hh;exact Option.some.inj hh
      subst a
      rw [hcoord j]
  have hint : ∀ (r : Fin (p + m)) (i : Fin p), MeasureTheory.Integrable
      (fun z : ℝ × ℝ => paramPinRowFun twenty N r z.1 * (paramPinColFun twenty N E i z.2 * paramPinKernel z.1 z.2))
      (realPlaceMeasure.prod (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow twenty N r.val (filteredColumn twenty N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [paramPinRowFun, paramPinColFun, paramPinKernel]
    ring

  let W : ℝ :=∏ j,|restrictedWeight twenty N (kv j) (CatalanMeasure.chebNode (18*N)) (av j)|
  have hW : 0 ≤ W :=prod_nonneg (fun j _ =>abs_nonneg _)
  have hae : ∀ᵐ w ∂(CatalanMeasure.pairMeasure realPlaceMeasure
      (volume.restrict (Ioo (0:ℝ) 1)) p),
      |CatalanMeasure.mixedDouble (paramPinRowFun twenty N) (realCoordinateInv ∘ yv)
        (paramPinColFun twenty N E) paramPinKernel w.1 w.2| * W ≤
      twentySheetPrefactor N*twentyAtomEnergyBound N m δ :=by
    filter_upwards [ae_pair_rectangle p] with w hw
    have hh :=hbound p m hpm E hE hEn kv av w.1 w.2 hw.1 hw.2
    have hy : realCoordinateInv ∘ yv=CatalanMeasure.chebNode (18*N) ∘ av :=by
      funext j
      exact hcoord j
    rw [hy]
    exact hh
  have hdet :=CatalanMeasure.abs_det_mixedMatrix_mul_weight_le
    realPlaceMeasure (volume.restrict (Ioo (0:ℝ) 1))
    (paramPinRowFun twenty N) (realCoordinateInv ∘ yv) (paramPinColFun twenty N E)
    paramPinKernel hW hint hae
  rw [← hmat,abs_det_submatrix_equiv,pairMeasure_real_univ] at hdet
  have hprodW : (∏ k,(f k).elim 1 (fun a =>|twentyAtomWeights N a k|))=W :=by
    rw [← e.prod_comp]
    rw [Fin.prod_univ_add]
    simp only [he1,Option.elim,prod_const_one,one_mul]
    apply prod_congr rfl
    intro j _
    simp only [hav,Option.elim,twentyAtomWeights,W,kv]
  rw [hprodW]
  let c :=twentyAtomColumnCost N
  have hprod : (∏ k,(f k).elim 1 (fun _ =>c))=c^m :=by
    have hh : ∀ k,(f k).elim 1 (fun _ =>c)=if P k then 1 else c :=by
      intro k
      simp only [P]
      rcases f k with _ | a <;> simp
    simp_rw [hh]
    rw [prod_ite,prod_const_one,one_mul,prod_const,hm,Fintype.card_subtype]
  rw [hprod]
  have h2p : (2:ℝ)^p ≤ (2:ℝ)^(twenty.n N) :=pow_le_pow_right₀ (by norm_num) (by omega)
  have hB : 0 ≤ twentySheetPrefactor N*twentyAtomEnergyBound N m δ :=by
    unfold twentySheetPrefactor twentyAtomEnergyBound
    positivity
  calc
    W*|(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyAtomVectors N) f).det| ≤
        (twentySheetPrefactor N*twentyAtomEnergyBound N m δ)*2^p :=by
      simpa only [mul_comm] using hdet
    _ ≤ (twentySheetPrefactor N*twentyAtomEnergyBound N m δ)*2^(twenty.n N) :=
      mul_le_mul_of_nonneg_left h2p hB
    _ = _ :=by
      unfold twentyAtomEnergyBound twentyAtomBaseBound c twentyAtomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m:ℝ))=Real.exp a*(Real.exp b)^m :=by
        rw [Real.exp_add,← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring

end
end CatalanMeasure.Parametric
