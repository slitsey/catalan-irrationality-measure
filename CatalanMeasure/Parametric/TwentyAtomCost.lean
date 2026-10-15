module

public import CatalanMeasure.Parametric.TwentyFirstCost
public import CatalanMeasure.Parametric.TwentyFullAtomDeterminants

@[expose] public section

namespace CatalanMeasure.Parametric

open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter
open scoped Topology BigOperators

noncomputable section

theorem twenty_first_marked_sheet_product_of_cost_eventually (c : ℝ)
    (hcost : TwentyFirstCostBudget c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      markedSheetProduct twenty N hpm x y s ≤
        ((3 / 2 : ℝ) ^ twenty.n N * (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2)) *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
            (20*c) * N * m) := by
  filter_upwards [twenty_first_marked_product_of_cost_eventually c hcost hε,
      Filter.eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  exact (marked_sheet_product_first_le twenty_admissible hN hpm x y s hx hx0 hy hy0 hs).trans
    (mul_le_mul_of_nonneg_left (he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase)
      (by positivity))

theorem twenty_marked_sheet_product_of_cost_eventually (c r : ℝ)
    (hcost : TwentyFirstCostBudget c) (hfc : 20*c ≤ r) (hsc : 89 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetProduct twenty N hpm x y s ≤
        (5 : ℝ) ^ m * twentySheetPrefactor N *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
            r * N * m) := by
  filter_upwards [twenty_first_marked_sheet_product_of_cost_eventually c hcost hε,
      twenty_second_marked_sheet_product_eventually hε] with N hfirst hsecond
  intro p m hpm x y s hx hx0 hy hy0 hs hzi hsi
  have hxi : Function.Injective x := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (hzi (by simpa using hij))
  have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
  have hH : 0 ≤ twentySheetPrefactor N := by unfold twentySheetPrefactor; positivity
  have hF : (3 / 2 : ℝ) ^ twenty.n N *
      (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2) ≤ twentySheetPrefactor N := by
    unfold twentySheetPrefactor
    exact le_add_of_nonneg_right (by positivity)
  have hI : (1 + 10 * Real.exp 12 * (twenty.n N : ℝ)) ^ twenty.n N ≤
      twentySheetPrefactor N := by
    unfold twentySheetPrefactor
    exact le_add_of_nonneg_left (by positivity)
  by_cases hcase : -1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)
  · have hh := hfirst p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
    apply hh.trans
    apply mul_le_mul
    · exact hF.trans (le_mul_of_one_le_left hH h5)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N*m := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hfc hNm]
    · exact (Real.exp_pos _).le
    · positivity
  · have hh := hsecond p m hpm x y s hx hx0 hy hy0 hs hzi hsi (le_of_not_gt hcase)
    apply hh.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hI (pow_nonneg (by norm_num) _)
    · apply Real.exp_le_exp.mpr
      have hNm : (0 : ℝ) ≤ N * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_right hsc hNm]
    · exact (Real.exp_pos _).le
    · positivity

def TwentyWeightedAtomPointHypothesis (ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (_hpm : p + m = twenty.n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < twenty.n N) →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin (18 * N)),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j, realCoordinateInv (y j) = CatalanMeasure.chebX (18 * N) (a j)) →
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun twenty N) (originalPolyAtoms twenty N y)
        (paramPinColFun twenty N E) paramPinKernel (realCoordinateInv ∘ x) s| *
        (∏ j, |restrictedWeight twenty N (k j) (CatalanMeasure.chebX (18 * N)) (a j)|) ≤
      twentySheetPrefactor N * (540000 * (N : ℝ)) ^ m *
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
          ρ * N * m)

theorem twenty_weighted_atom_point_of_cost (c r w : ℝ)
    (hcost : TwentyFirstCostBudget c) (hfc : 20*c ≤ r) (hsc : 89 ≤ r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin (18*N)),
      |(rowCommonFactor twenty N).eval (CatalanMeasure.chebX (18*N) a)| *
        |restrictedWeight twenty N k (CatalanMeasure.chebX (18*N)) a| ≤
          108000*(N : ℝ)*Real.exp (w*N)) : TwentyWeightedAtomPointHypothesis (r+w) := by
  intro ε hε
  filter_upwards [twenty_marked_sheet_product_of_cost_eventually c r hcost hfc hsc hε,
      hweights, eventually_gt_atTop (0 : ℕ)]
    with N hsheet hw hN p m hpm E hEi hEn x y s k a hx hx0 hy hy0 hs hzi hsi hcoord
  let β := fun j => restrictedWeight twenty N (k j) (CatalanMeasure.chebX (18 * N)) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| * |β j| ≤ Q := by
    rw [hcoord j]
    exact hw (k j) (a j)
  have hbase := original_poly_atoms_mixedDouble_mul_weight_le twenty_admissible hN hpm
    E hEi hEn x y s β hx hx0 hy hy0 hs hweight
  have hp := hsheet p m hpm x y s hx hx0 hy hy0 hs hzi hsi
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp ((20 * (N : ℝ)) ^ 2 *
      (-twentyDualTarget + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp ((20 * (N : ℝ)) ^ 2 *
        (-twentyDualTarget + Real.log 2 / 2 + ε) + (r+w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetProduct twenty N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * twentySheetPrefactor N *
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = twentySheetPrefactor N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp ((20 * (N : ℝ)) ^ 2 * (-twentyDualTarget + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]

def twentyParametricAtomColumnCost (ρ : ℝ) (N : ℕ) : ℝ :=
  540000*(N : ℝ)*Real.exp (ρ*N)

theorem twenty_weighted_atom_det_of_point_eventually (ρ : ℝ)
    (hpoint : TwentyWeightedAtomPointHypothesis ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (twenty.n N) → Option (Fin (18*N)),
      (∏ k, (f k).elim 1 (fun a => |twentyFullAtomWeights N a k|)) *
        |(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (twentyFullAtomVectors N) f).det| ≤
      twentyAtomBaseBound N ε * ∏ k, (f k).elim 1 (fun _ => twentyParametricAtomColumnCost ρ N) := by
  filter_upwards [hpoint ε hε,
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
      ∏ k, (f k).elim 1 (fun _ => twentyParametricAtomColumnCost ρ N) := by
    apply mul_nonneg
    · unfold twentyAtomBaseBound twentySheetPrefactor
      positivity
    · apply prod_nonneg
      intro k _
      cases f k <;> dsimp [twentyParametricAtomColumnCost] <;> positivity
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
    Real.exp ((20*(N : ℝ))^2*(-twentyDualTarget+Real.log 2/2+ε)+ρ*N*m)
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
  let c := twentyParametricAtomColumnCost ρ N
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
      unfold Bd twentyAtomBaseBound c twentyParametricAtomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m : ℝ)) = Real.exp a * (Real.exp b)^m := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring

end
end CatalanMeasure.Parametric
