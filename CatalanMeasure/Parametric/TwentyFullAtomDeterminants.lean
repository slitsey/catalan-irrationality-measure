module

public import CatalanMeasure.Parametric.TwentyMarkedIntegrand
public import CatalanMeasure.Parametric.MarkedAtomAlmostEverywhere
public import CatalanMeasure.Parametric.TwentyAtomDeterminants

@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter
open scoped BigOperators Topology
noncomputable section

def twentyFullAtomVectors (N : ℕ) : Fin (twenty.n N) → Fin (18*N) → ℝ :=
  fun r a => (realPoly (rowP twenty N r.val)).eval (CatalanMeasure.chebX (18*N) a)

def twentyFullAtomWeights (N : ℕ) : Fin (18*N) → Fin (twenty.n N) → ℝ :=
  fun a k => restrictedWeight twenty N k.val (CatalanMeasure.chebX (18*N)) a

def twentyFullAtomColumnCost (N : ℕ) : ℝ :=
  540000 * (N : ℝ) * Real.exp (108 * (N : ℝ))

theorem twenty_full_delta_matrix_eq {N : ℕ} (hN : 0 < N) (x : ℝ) :
    aeval x (deltaPoly twenty N) =
      (Matrix.of fun r k : Fin (twenty.n N) => twentyRealBaseMatrix N r k +
        (x-catalan) * ∑ a, twentyFullAtomVectors N r a * twentyFullAtomWeights N a k).det := by
  have hh := AlgHom.map_det (aeval (R := ℚ) x)
    ((X : ℚ[X]) • (measureCatalanMatrix twenty N).map C + (measureBaseMatrix twenty N).map C)
  unfold deltaPoly
  rw [hh]
  congr 1
  ext r k
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, deltaPoly_matrix_entry]
  simp only [map_add, map_mul, aeval_X, aeval_C, eq_ratCast, Matrix.of_apply,
    twentyRealBaseMatrix, twentyFullAtomVectors, twentyFullAtomWeights]
  rw [← twenty_full_weight_formula hN r.isLt k.val,
    ← filteredEntry_real_affine twenty_admissible hN r.isLt k.isLt]
  ring

/-- Integrating the marked bound preserves the original P-only fixed atoms.
Repeated fixed atoms give identical columns. Free/fixed collisions are
excluded only on a null set; they are not asserted to give equal columns. -/
theorem twenty_weighted_full_atomMatrix_det_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (twenty.n N) → Option (Fin (18*N)),
      (∏ k, (f k).elim 1 (fun a => |twentyFullAtomWeights N a k|)) *
        |(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyFullAtomVectors N) f).det| ≤
      twentyAtomBaseBound N ε * ∏ k, (f k).elim 1 (fun _ => twentyFullAtomColumnCost N) := by
  filter_upwards [twenty_original_poly_atoms_weighted_eventually hε,
    eventually_gt_atTop (0 : ℕ)] with N hbound hN f
  classical
  let P : Fin (twenty.n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // P k} + Fintype.card {k // ¬ P k} = twenty.n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le P
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // P k} with hp
  set m := Fintype.card {k // ¬ P k} with hm
  let e : Fin (p+m) ≃ Fin (twenty.n N) :=
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
    intro i j hij
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hij))
  have hEn : ∀ i, E i < twenty.n N := fun i => (e (Fin.castAdd m i)).isLt
  let av : Fin m → Fin (18*N) := fun j =>
    Classical.choose (Option.ne_none_iff_exists'.mp (he2 j))
  have hav (j : Fin m) : f (e (Fin.natAdd p j)) = some (av j) :=
    Classical.choose_spec (Option.ne_none_iff_exists'.mp (he2 j))
  have hR : 0 ≤ twentyAtomBaseBound N ε *
      ∏ k, (f k).elim 1 (fun _ => twentyFullAtomColumnCost N) := by
    apply mul_nonneg
    · unfold twentyAtomBaseBound twentySheetPrefactor
      positivity
    · apply prod_nonneg
      intro k _
      cases f k <;> dsimp [twentyFullAtomColumnCost] <;> positivity
  by_cases hai : Function.Injective av
  swap
  · have hex : ∃ i j, av i = av j ∧ i ≠ j := by
      by_contra hh
      apply hai
      intro i j hij
      by_contra hne
      exact hh ⟨i, j, hij, hne⟩
    obtain ⟨i, j, hij, hne⟩ := hex
    have hcol : e (Fin.natAdd p i) ≠ e (Fin.natAdd p j) := by
      intro h
      exact hne (Fin.natAdd_injective _ _ (e.injective h))
    have hd : (CatalanMeasure.atomMatrix (twentyRealBaseMatrix N)
        (twentyFullAtomVectors N) f).det = 0 := by
      apply Matrix.det_zero_of_column_eq hcol
      intro r
      simp only [CatalanMeasure.atomMatrix, Matrix.of_apply, hav, Option.elim, hij]
    rw [hd, abs_zero, mul_zero]
    exact hR
  let kv : Fin m → ℕ := fun j => (e (Fin.natAdd p j)).val
  let yv : Fin m → ℝ := fun j => realCoordinate (CatalanMeasure.chebX (18*N) (av j))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 1 :=
    fun j => realCoordinate_mem (CatalanMeasure.chebX_mem (av j))
  have hcoord (j : Fin m) : realCoordinateInv (yv j) =
      CatalanMeasure.chebX (18*N) (av j) :=
    realCoordinate_right_inverse (CatalanMeasure.chebX_mem (av j))
  have hyv0 : ∀ j, yv j ≠ 0 := by
    intro j hj
    have hz := hcoord j
    rw [hj] at hz
    exact chebX_even_ne_zero ⟨9*N, by omega⟩ (av j)
      (by simpa [realCoordinateInv] using hz.symm)
  have hyi : Function.Injective yv := by
    intro i j hij
    apply hai
    apply CatalanMeasure.chebX_injective (18*N)
    rw [← hcoord i, ← hcoord j, hij]
  have hmat : (CatalanMeasure.atomMatrix (twentyRealBaseMatrix N)
      (twentyFullAtomVectors N) f).submatrix (finCongr hpm) e =
      CatalanMeasure.mixedMatrixWithAtoms realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1))
        (paramPinRowFun twenty N) (originalPolyAtoms twenty N yv)
        (paramPinColFun twenty N E) paramPinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_left, twentyRealBaseMatrix]
      rw [realEntry_eq_realPlace_product twenty]
      congr 1
      funext z
      simp only [paramPinRowFun, paramPinColFun, paramPinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, hav j,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_right,
        twentyFullAtomVectors, originalPolyAtoms, finCongr_apply, Fin.val_cast]
      rw [hcoord j]
  have hint : ∀ (r : Fin (p+m)) (i : Fin p), Integrable
      (fun z : ℝ × ℝ => paramPinRowFun twenty N r z.1 *
        (paramPinColFun twenty N E i z.2 * paramPinKernel z.1 z.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow twenty N r.val (filteredColumn twenty N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [paramPinRowFun, paramPinColFun, paramPinKernel]
    ring
  let W : ℝ := ∏ j, |restrictedWeight twenty N (kv j) (CatalanMeasure.chebX (18*N)) (av j)|
  let Bd : ℝ := twentySheetPrefactor N * (540000*(N : ℝ))^m *
    Real.exp ((20*(N : ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε)+108*N*m)
  have hW : 0 ≤ W := prod_nonneg (fun j _ => abs_nonneg _)
  have hae : ∀ᵐ w ∂CatalanMeasure.pairMeasure realPlaceMeasure
      (volume.restrict (Ioo (0 : ℝ) 1)) p,
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun twenty N)
        (originalPolyAtoms twenty N yv) (paramPinColFun twenty N E) paramPinKernel w.1 w.2| * W ≤ Bd := by
    filter_upwards [ae_marked_atom_geometry p yv hyi] with w hw
    rcases hw with ⟨ht, ht0, hx, hx0, hs, hzi, hsi⟩
    let x : Fin p → ℝ := realCoordinate ∘ w.1
    have htx : w.1 = realCoordinateInv ∘ x := by
      funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    rw [htx]
    exact hbound p m hpm E hE hEn x yv w.2 kv av
      hx hx0 hyv hyv0 hs hzi hsi hcoord
  have hdet := CatalanMeasure.abs_det_mixedMatrixWithAtoms_mul_weight_le
    realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1)) (paramPinRowFun twenty N)
    (originalPolyAtoms twenty N yv) (paramPinColFun twenty N E) paramPinKernel hW hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  have hprodW : (∏ k, (f k).elim 1 (fun a => |twentyFullAtomWeights N a k|)) = W := by
    rw [← e.prod_comp, Fin.prod_univ_add]
    simp only [he1, Option.elim, prod_const_one, one_mul]
    apply prod_congr rfl
    intro j _
    simp only [hav, Option.elim, twentyFullAtomWeights, W, kv]
  rw [hprodW]
  let c := twentyFullAtomColumnCost N
  have hprod : (∏ k, (f k).elim 1 (fun _ => c)) = c^m := by
    have hh : ∀ k, (f k).elim 1 (fun _ => c) = if P k then 1 else c := by
      intro k
      simp only [P]
      rcases f k with _ | a <;> simp
    simp_rw [hh]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have h2p : (2 : ℝ)^p ≤ (2 : ℝ)^(twenty.n N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd : 0 ≤ Bd := by unfold Bd twentySheetPrefactor; positivity
  calc
    W * |(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyFullAtomVectors N) f).det| ≤
        Bd * 2^p := by simpa only [mul_comm] using hdet
    _ ≤ Bd * 2^(twenty.n N) := mul_le_mul_of_nonneg_left h2p hBd
    _ = _ := by
      unfold Bd twentyAtomBaseBound c twentyFullAtomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m : ℝ)) = Real.exp a * (Real.exp b)^m := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring

end
end CatalanMeasure.Parametric
