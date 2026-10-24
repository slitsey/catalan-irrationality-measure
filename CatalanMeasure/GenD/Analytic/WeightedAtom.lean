module

public import CatalanMeasure.GenD.Analytic.AtomBase
public import CatalanMeasure.GenD.Analytic.MarkedMixedMajorant
public import CatalanMeasure.Parametric.MarkedAtomAlmostEverywhere
public import CatalanMeasure.Lemma6

@[expose] public section

/-!
# Analytic layer, group 3: weighted atom points and the atom determinant bound

Generic versions of `GapAtomCost`:

* `MarkedSheetBound P G target r` -- the output of group 2's `marked_sheet_on`
  (`markedSheetProduct ≤ 5^m · sheetPrefactor · exp((n0 N)² (-target + log 2/2 + ε) + r N m)`);
* `WeightedAtomPoint P τ G target ρ` -- generic `WeightedAtomPointOn`;
* `weighted_atom_point_of_sheet` -- generic `weighted_atom_point_on` from the sheet bound and
  the node-weight bound (group 4's `GapWeightBounds`);
* `weighted_atom_det` -- generic `weighted_atom_det_on`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial OAI.InternalCatalan Set Finset MeasureTheory Matrix Filter CatalanMeasure.Parametric
open scoped Topology BigOperators

noncomputable section

/-- Output of group 2's `marked_sheet_on`. -/
def MarkedSheetBound (P : Parameters) (G : ℝ → Prop) (target r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetProduct P N hpm x y s ≤
        (5 : ℝ) ^ m * sheetPrefactor P N *
          Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m)

def WeightedAtomPoint (P : Parameters) (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop) (target ρ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (_hpm : p + m = P.n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < P.n N) →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ)
        (k : Fin m → ℕ) (a : Fin m → Fin ((P.n0 - P.g0) * N)),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      (∀ j, realCoordinateInv (y j) = τ N (a j)) →
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N) (originalPolyAtoms P N y)
        (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| *
        (∏ j, |restrictedWeight P N (k j) (τ N) (a j)|) ≤
      sheetPrefactor P N * (540000 * (N : ℝ)) ^ m *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          ρ * N * m)

theorem weighted_atom_point_of_sheet {target r w : ℝ} (P : Parameters) (hP : Admissible P)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hsheet : MarkedSheetBound P G target r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (τ N a)| *
        |restrictedWeight P N k (τ N) a| ≤
          108000*(N : ℝ)*Real.exp (w*N)) : WeightedAtomPoint P τ G target (r + w) := by
  intro ε hε
  filter_upwards [hsheet ε hε,
      hweights, eventually_gt_atTop (0 : ℕ)]
    with N hsheet_N hw hN p m hpm E hEi hEn x y s k a hx hx0 hy hy0 hGy hs hzi hsi hcoord
  let β := fun j => restrictedWeight P N (k j) (τ N) (a j)
  let Q : ℝ := 108000 * N * Real.exp (w * N)
  have hweight (j : Fin m) :
      |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| ≤ Q := by
    rw [hcoord j]
    exact hw (k j) (a j)
  have hbase := original_poly_atoms_mixedDouble_mul_weight_le hP hN hpm
    E hEi hEn x y s β hx hx0 hy hy0 hs hweight
  have hp := hsheet_N p m hpm x y s hx hx0 hy hy0 hGy hs hzi hsi
  have hQ : 0 ≤ Q ^ m := by dsimp [Q]; positivity
  have hc : (5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m = (540000 * (N : ℝ)) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have he : Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
      (-target + Real.log 2 / 2 + ε) + r * N * m) *
      Real.exp (w * (N : ℝ)) ^ m =
      Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 *
        (-target + Real.log 2 / 2 + ε) + (r+w) * N * m) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ markedSheetProduct P N hpm x y s * Q ^ m := hbase
    _ ≤ ((5 : ℝ) ^ m * sheetPrefactor P N *
        Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m)) * Q ^ m := mul_le_mul_of_nonneg_right hp hQ
    _ = sheetPrefactor P N * ((5 : ℝ) ^ m * (108000 * (N : ℝ)) ^ m) *
        (Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          r * N * m) * Real.exp (w * (N : ℝ)) ^ m) := by
      dsimp [Q]
      rw [mul_pow]
      ring
    _ = _ := by rw [hc, he]

/-- Generic `weighted_atom_det_on`: the atom determinants are bounded by the weighted atom point. -/
theorem weighted_atom_det (P : Parameters)
    (τ : (N : ℕ) → Fin ((P.n0 - P.g0) * N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPoint P τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (P.n N) → Option (Fin ((P.n0 - P.g0) * N)),
      (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) *
        |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
      atomBaseBoundAt P target N ε * ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
  filter_upwards [hpoint ε hε,
    eventually_gt_atTop (0 : ℕ)] with N hbound hN f
  classical
  let Pr : Fin (P.n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // Pr k} + Fintype.card {k // ¬ Pr k} = P.n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le Pr
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // Pr k} with hp
  set m := Fintype.card {k // ¬ Pr k} with hm
  let e : Fin (p+m) ≃ Fin (P.n N) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin {k // Pr k}).symm
      (Fintype.equivFin {k // ¬ Pr k}).symm)).trans (Equiv.sumCompl Pr)
  have he1 : ∀ i : Fin p, f (e (Fin.castAdd m i)) = none := by
    intro i
    have h : e (Fin.castAdd m i) = ((Fintype.equivFin {k // Pr k}).symm i).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // Pr k}).symm i).property
  have he2 : ∀ j : Fin m, f (e (Fin.natAdd p j)) ≠ none := by
    intro j
    have h : e (Fin.natAdd p j) = ((Fintype.equivFin {k // ¬ Pr k}).symm j).val := by
      simp only [e, Equiv.trans_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [h]
    exact ((Fintype.equivFin {k // ¬ Pr k}).symm j).property
  let E : Fin p → ℕ := fun i => (e (Fin.castAdd m i)).val
  have hE : Function.Injective E := by
    intro i j hij
    exact Fin.castAdd_injective _ _ (e.injective (Fin.ext hij))
  have hEn : ∀ i, E i < P.n N := fun i => (e (Fin.castAdd m i)).isLt
  let av : Fin m → Fin ((P.n0 - P.g0) * N) := fun j =>
    Classical.choose (Option.ne_none_iff_exists'.mp (he2 j))
  have hav (j : Fin m) : f (e (Fin.natAdd p j)) = some (av j) :=
    Classical.choose_spec (Option.ne_none_iff_exists'.mp (he2 j))
  have hR : 0 ≤ atomBaseBoundAt P target N ε *
      ∏ k, (f k).elim 1 (fun _ => atomColumnCost ρ N) := by
    apply mul_nonneg
    · unfold atomBaseBoundAt sheetPrefactor
      positivity
    · apply prod_nonneg
      intro k _
      cases f k <;> dsimp [atomColumnCost] <;> positivity
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
    have hd : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
        (nodeAtomVectors P τ N) f).det = 0 := by
      apply Matrix.det_zero_of_column_eq hcol
      intro r
      simp only [CatalanMeasure.atomMatrix, Matrix.of_apply, hav, Option.elim, hij]
    rw [hd, abs_zero, mul_zero]
    exact hR
  let kv : Fin m → ℕ := fun j => (e (Fin.natAdd p j)).val
  let yv : Fin m → ℝ := fun j => realCoordinate (τ N (av j))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 1 :=
    fun j => realCoordinate_mem (hτmem N (av j))
  have hcoord (j : Fin m) : realCoordinateInv (yv j) =
      τ N (av j) :=
    realCoordinate_right_inverse (hτmem N (av j))
  have hyv0 : ∀ j, yv j ≠ 0 := by
    intro j hj
    have hz := hcoord j
    rw [hj] at hz
    exact hτzero N (av j)
      (by simpa [realCoordinateInv] using hz.symm)
  have hyi : Function.Injective yv := by
    intro i j hij
    apply hai
    apply hτinj N
    rw [← hcoord i, ← hcoord j, hij]
  have hmat : (CatalanMeasure.atomMatrix (realBaseMatrix P N)
      (nodeAtomVectors P τ N) f).submatrix (finCongr hpm) e =
      CatalanMeasure.mixedMatrixWithAtoms realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1))
        (paramPinRowFun P N) (originalPolyAtoms P N yv)
        (paramPinColFun P N E) paramPinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_left, realBaseMatrix]
      rw [realEntry_eq_realPlace_product P]
      congr 1
      funext z
      simp only [paramPinRowFun, paramPinColFun, paramPinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, hav j,
        Option.elim, CatalanMeasure.mixedMatrixWithAtoms, Fin.addCases_right,
        nodeAtomVectors, originalPolyAtoms, finCongr_apply, Fin.val_cast]
      rw [hcoord j]
  have hint : ∀ (r : Fin (p+m)) (i : Fin p), Integrable
      (fun z : ℝ × ℝ => paramPinRowFun P N r z.1 *
        (paramPinColFun P N E i z.2 * paramPinKernel z.1 z.2))
      (realPlaceMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow P N r.val (filteredColumn P N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [paramPinRowFun, paramPinColFun, paramPinKernel]
    ring
  let W : ℝ := ∏ j, |restrictedWeight P N (kv j) (τ N) (av j)|
  let Bd : ℝ := sheetPrefactor P N * (540000*(N : ℝ))^m *
    Real.exp (((P.n0 : ℝ) * (N : ℝ)) ^ 2*(-target+Real.log 2/2+ε)+ρ*N*m)
  have hW : 0 ≤ W := prod_nonneg (fun j _ => abs_nonneg _)
  have hae : ∀ᵐ w ∂CatalanMeasure.pairMeasure realPlaceMeasure
      (volume.restrict (Ioo (0 : ℝ) 1)) p,
      |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N)
        (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel w.1 w.2| * W ≤ Bd := by
    filter_upwards [ae_marked_atom_geometry p yv hyi] with w hw
    rcases hw with ⟨ht, ht0, hx, hx0, hs, hzi, hsi⟩
    let x : Fin p → ℝ := realCoordinate ∘ w.1
    have htx : w.1 = realCoordinateInv ∘ x := by
      funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    rw [htx]
    exact hbound p m hpm E hE hEn x yv w.2 kv av
      hx hx0 hyv hyv0 (fun j => hτG N (av j)) hs hzi hsi hcoord
  have hdet := CatalanMeasure.abs_det_mixedMatrixWithAtoms_mul_weight_le
    realPlaceMeasure (volume.restrict (Ioo (0 : ℝ) 1)) (paramPinRowFun P N)
    (originalPolyAtoms P N yv) (paramPinColFun P N E) paramPinKernel hW hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  have hprodW : (∏ k, (f k).elim 1 (fun a => |nodeAtomWeights P τ N a k|)) = W := by
    rw [← e.prod_comp, Fin.prod_univ_add]
    simp only [he1, Option.elim, prod_const_one, one_mul]
    apply prod_congr rfl
    intro j _
    simp only [hav, Option.elim, nodeAtomWeights, W, kv]
  rw [hprodW]
  let c := atomColumnCost ρ N
  have hprod : (∏ k, (f k).elim 1 (fun _ => c)) = c^m := by
    have hh : ∀ k, (f k).elim 1 (fun _ => c) = if Pr k then 1 else c := by
      intro k
      simp only [Pr]
      rcases f k with _ | a <;> simp
    simp_rw [hh]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have h2p : (2 : ℝ)^p ≤ (2 : ℝ)^(P.n N) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd : 0 ≤ Bd := by unfold Bd sheetPrefactor; positivity
  calc
    W * |(CatalanMeasure.atomMatrix (realBaseMatrix P N) (nodeAtomVectors P τ N) f).det| ≤
        Bd * 2^p := by simpa only [mul_comm] using hdet
    _ ≤ Bd * 2^(P.n N) := mul_le_mul_of_nonneg_left h2p hBd
    _ = _ := by
      unfold Bd atomBaseBoundAt c atomColumnCost
      have he (a b : ℝ) : Real.exp (a+b*(m : ℝ)) = Real.exp a * (Real.exp b)^m := by
        rw [Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      simp only [mul_pow]
      ring


end

end Analytic
end CatalanMeasure.GenD
