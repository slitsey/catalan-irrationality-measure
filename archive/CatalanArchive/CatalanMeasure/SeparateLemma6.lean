module
public import CatalanArchive.CatalanMeasure.SeparateFixedMajorant
public import CatalanArchive.CatalanMeasure.SeparateBounds
public import CatalanArchive.CatalanMeasure.FixedNodeLemma6
@[expose] public section
open Set Finset Real Filter Polynomial Matrix MeasureTheory
open scoped BigOperators Nat
namespace OAI.InternalCatalan
theorem separate_mixedDouble_uniform_bound {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (p m : ℕ) (hpm : p + m = n N)
      (E : Fin p → ℕ), Function.Injective E → (∀ i, E i < n N) →
      ∀ y : Fin m → ℝ, (∀ j, y j ∈ Ioo (-1 : ℝ) 0) →
      ∀ t s : Fin p → ℝ, (∀ i, t i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ y) (pinColFun N E)
          pinKernel t s| ≤
        realDeterminantSheetPrefactor N * (fixedNodeCap N) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
          Real.exp ((n N : ℝ) * m * separateEnergyCost) := by
  obtain ⟨N₁, h₁⟩ := separate_case_one_eventually hd
  obtain ⟨N₂, h₂⟩ := weighted_case_two_eventually hd
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro N hN p m hpm E hE hEn y hy t s ht hs
  have hcap0 : 0 < fixedNodeCap N := Real.exp_pos _
  have hN0 : 0 < N := by omega
  have hp : p ≤ n N := by omega
  have hn : (0 : ℝ) < n N := by exact_mod_cast (show 0 < n N by unfold n; omega)
  have hmR : (m : ℝ) = (n N : ℝ) - p := by
    rw [← hpm]
    push_cast
    ring
  set RHS := realDeterminantSheetPrefactor N * (fixedNodeCap N) ^ m *
      Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
      Real.exp ((n N : ℝ) * m * separateEnergyCost) with hRHS
  have hRHS0 : 0 ≤ RHS := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  -- degenerate configurations
  by_cases hzero : ∃ i, t i = 0
  · obtain ⟨i, hti⟩ := hzero
    rw [mixedDouble_eq_zero_of_rowDet (rowDet_eq_zero_of_zero hN0 hpm _ t hti), abs_zero]
    exact hRHS0
  push Not at hzero
  by_cases hsi : Function.Injective s
  swap
  · rw [mixedDouble_eq_zero_of_s hsi, abs_zero]
    exact hRHS0
  -- coordinates
  obtain ⟨x, rfl, hx, hx0⟩ : ∃ x : Fin p → ℝ, t = realCoordinateInv ∘ x ∧
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ i, x i ≠ 0) := by
    refine ⟨realCoordinate ∘ t, ?_, fun i => realCoordinate_mem (ht i), fun i => ?_⟩
    · funext i
      exact (realCoordinate_right_inverse (ht i)).symm
    · intro h0
      apply hzero i
      rw [← realCoordinate_right_inverse (ht i)]
      simp only [Function.comp_apply] at h0
      rw [h0]
      simp [realCoordinateInv]
  by_cases hzi : Function.Injective (Fin.append x y)
  swap
  · have hni : ¬ Function.Injective (Fin.append (realCoordinateInv ∘ x) (realCoordinateInv ∘ y)) := by
      rw [fin_append_comp]
      exact fun hinj => hzi (hinj.of_comp)
    rw [mixedDouble_eq_zero_of_rowDet (rowDet_eq_zero_of_not_injective _ _ hni), abs_zero]
    exact hRHS0
  have hxi : Function.Injective x := by
    intro i i' hii
    have := hzi (a₁ := Fin.castAdd m i) (a₂ := Fin.castAdd m i') (by simpa using hii)
    exact Fin.castAdd_injective _ _ this
  have hfinal : ∀ (K V : ℝ), 0 ≤ K → K ≤ realDeterminantSheetPrefactor N →
      V ≤ -(229180925 / 100000000 : ℝ) + d + ((n N : ℝ) - p) / (n N : ℝ) * separateEnergyCost →
      K * (fixedNodeCap N) ^ m *
        Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2)) ≤ RHS := by
    intro K V hK0 hK hV
    rw [hRHS, mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    have hexp : Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2)) ≤
        Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2) +
          (n N : ℝ) * m * separateEnergyCost) := by
      apply Real.exp_le_exp.mpr
      have h2 : (n N : ℝ) ^ 2 * (((n N : ℝ) - p) / (n N : ℝ) * separateEnergyCost) =
          (n N : ℝ) * m * separateEnergyCost := by
        rw [hmR]
        field_simp
      nlinarith [sq_nonneg (n N : ℝ)]
    calc K * (fixedNodeCap N) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (V + Real.log 2 / 2))
        ≤ realDeterminantSheetPrefactor N * (fixedNodeCap N) ^ m *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2) +
            (n N : ℝ) * m * separateEnergyCost) := by
          have hsp := realDeterminantSheetPrefactor_nonneg N
          gcongr
      _ = _ := by ring
  by_cases hcase : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
      (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) ≤ ((n N - 1 - 2 * g N : ℕ) : ℝ)
  · have hb := separate_mixedDouble_le_caseTwo_product hN0 hpm E hE hEn x y s hx hx0 hy hs hxi hsi hzi hcase
    rw [separate_pin_majorant_eq hN0 hpm _ 2 x s hs] at hb
    have hdual := h₂ N (by omega) p hp x s hx hs hx0 hxi hsi
    have hcomp := separate_cap_compensated hN0 hpm (by positivity : (0 : ℝ) ≤ (1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N)
      (pinWeightedValue N 2 (((n N : ℝ) - p)/(n N : ℝ)) x s)
    apply (hb.trans hcomp).trans
    apply hfinal _ _ (by positivity) (le_max_left _ _)
    unfold separateEnergyCost
    unfold weightedEnergyCost at hdual
    linarith
  · have hb := fixed_mixedDouble_le_caseOne_product hN0 hpm E hE hEn x y s hx hx0 hy hs hxi hsi
    have hsplit : (∑ c : Fin (n N), (1 - (Fin.append x y (Fin.cast hpm.symm c)) ^ 2) /
        (1 + (Fin.append x y (Fin.cast hpm.symm c)) ^ 2)) =
        (∑ i, (1 - x i ^ 2) / (1 + x i ^ 2)) + ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) := by
      rw [sum_fin_cast hpm (fun c => (1 - (Fin.append x y c) ^ 2) / (1 + (Fin.append x y c) ^ 2)),
        Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    have hyw : ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) ≤ (m : ℝ) := by
      calc ∑ j, (1 - y j ^ 2) / (1 + y j ^ 2) ≤ ∑ _j : Fin m, (1 : ℝ) := by
            apply sum_le_sum
            intro j _
            rw [div_le_one (by positivity)]
            nlinarith [sq_nonneg (y j)]
        _ = m := by simp
    have hcond : ((n N - 1 - 2 * g N : ℕ) : ℝ) - ((n N : ℝ) - p) <
        ∑ i, (1 - x i ^ 2) / (1 + x i ^ 2) := by
      push Not at hcase
      rw [hsplit] at hcase
      rw [← hmR]
      linarith
    rw [fixed_pin_majorant_eq hN0 hpm _ 1 x s hs] at hb
    have hdual := h₁ N (by omega) p hp x s hx hs hx0 hxi hsi hcond
    exact hb.trans (hfinal _ _ (by positivity) (le_max_right _ _) hdual)


theorem separate_atomMatrix_det_bound {d : ℝ} (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : Fin (n N) → Option (Fin (H N)),
      |(CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).det| ≤
        ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2))) *
        ∏ k, (f k).elim 1 (fun _ => fixedNodeCap N *
          Real.exp ((n N : ℝ) * separateEnergyCost)) := by
  obtain ⟨N₀, hN₀⟩ := separate_mixedDouble_uniform_bound hd
  refine ⟨N₀, fun N hN f => ?_⟩
  classical
  have hcap0 : 0 < fixedNodeCap N := Real.exp_pos _
  let P : Fin (n N) → Prop := fun k => f k = none
  have hpm : Fintype.card {k // P k} + Fintype.card {k // ¬ P k} = n N := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have := Fintype.card_subtype_le P
    rw [Fintype.card_fin] at this
    omega
  set p := Fintype.card {k // P k} with hp
  set m := Fintype.card {k // ¬ P k} with hm
  let e : Fin (p + m) ≃ Fin (n N) :=
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
  have hEn : ∀ i, E i < n N := fun i => (e (Fin.castAdd m i)).isLt
  let yv : Fin m → ℝ := fun j =>
    (f (e (Fin.natAdd p j))).elim (-1 / 2) (fun a => realCoordinate (quadNode (H N) a))
  have hyv : ∀ j, yv j ∈ Ioo (-1 : ℝ) 0 := by
    intro j
    simp only [yv]
    rcases f (e (Fin.natAdd p j)) with _ | a
    · norm_num
    · exact quadNode_coordinate_mem _ a
  have hmat : (CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).submatrix
      (finCongr hpm) e =
      CatalanMeasure.mixedMatrix realPlaceMeasure (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))
        (pinRowFun N) (realCoordinateInv ∘ yv) (pinColFun N E) pinKernel := by
    ext r c
    refine Fin.addCases (fun i => ?_) (fun j => ?_) c
    · simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, he1 i,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_left, baseMatrix]
      rw [determinantEntry_eq_realPlace_product]
      congr 1
      funext z
      simp only [pinRowFun, pinColFun, pinKernel, E, finCongr_apply, Fin.val_cast]
      ring
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (he2 j)
      have hτ := quadNode_mem (H N) a
      simp only [Matrix.submatrix_apply, CatalanMeasure.atomMatrix, Matrix.of_apply, ha,
        Option.elim, CatalanMeasure.mixedMatrix, Fin.addCases_right, atomVectors, pinRowFun,
        Function.comp_apply, yv, finCongr_apply, Fin.val_cast]
      rw [realCoordinate_right_inverse ⟨hτ.1, by linarith [hτ.2]⟩]
  have hint : ∀ (r : Fin (p + m)) (i : Fin p), MeasureTheory.Integrable
      (fun z : ℝ × ℝ => pinRowFun N r z.1 * (pinColFun N E i z.2 * pinKernel z.1 z.2))
      (realPlaceMeasure.prod (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1))) := by
    intro r i
    refine (integrable_realPlaceRow N r.val (filteredColumn N (E i))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [pinRowFun, pinColFun, pinKernel]
    ring
  set Bd := realDeterminantSheetPrefactor N * (fixedNodeCap N) ^ m *
      Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + d + Real.log 2 / 2)) *
      Real.exp ((n N : ℝ) * m * separateEnergyCost) with hBd
  have hae : ∀ᵐ w ∂(CatalanMeasure.pairMeasure realPlaceMeasure
      (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) p),
      |CatalanMeasure.mixedDouble (pinRowFun N) (realCoordinateInv ∘ yv) (pinColFun N E)
        pinKernel w.1 w.2| ≤ Bd := by
    filter_upwards [ae_pair_rectangle p] with w hw
    exact hN₀ N hN p m hpm E hE hEn yv hyv w.1 w.2 hw.1 hw.2
  have hdet := CatalanMeasure.abs_det_mixedMatrix_le (realCoordinateInv ∘ yv) hint hae
  rw [← hmat, abs_det_submatrix_equiv, pairMeasure_real_univ] at hdet
  -- the product over the columns
  set c : ℝ := fixedNodeCap N * Real.exp ((n N : ℝ) * separateEnergyCost) with hc
  have hprod : ∏ k, (f k).elim 1 (fun _ => c) = c ^ m := by
    have : ∀ k, (f k).elim 1 (fun _ => c) = if P k then 1 else c := by
      intro k
      simp only [P]
      rcases f k with _ | a <;> simp
    simp_rw [this]
    rw [prod_ite, prod_const_one, one_mul, prod_const, hm, Fintype.card_subtype]
  rw [hprod]
  have hcm : c ^ m = (fixedNodeCap N) ^ m *
      Real.exp ((n N : ℝ) * m * separateEnergyCost) := by
    rw [hc, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have h2p : (2 : ℝ) ^ p ≤ (2 : ℝ) ^ n N := pow_le_pow_right₀ (by norm_num) (by omega)
  have hBd0 : 0 ≤ Bd := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  calc |(CatalanMeasure.atomMatrix (baseMatrix N) (atomVectors N) f).det| ≤ Bd * 2 ^ p := hdet
    _ ≤ Bd * 2 ^ n N := mul_le_mul_of_nonneg_left h2p hBd0
    _ = _ := by
        rw [hcm, hBd]
        ring


noncomputable def separateRho : ℝ := 3663 / 10

theorem separate_rho_condition {N : ℕ} (hN : 4000 ≤ N) :
    (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N) *
      (fixedNodeCap N * Real.exp ((n N : ℝ) * separateEnergyCost)) ≤
      Real.exp (separateRho * N) := by
  have hcap0 : 0 < fixedNodeCap N := Real.exp_pos _
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hl := Real.log_two_gt_d9
  have hc : separateEnergyCost ≤ 573 / 100 := le_rfl
  have hK0 : (0 : ℝ) ≤ (CatalanMeasure.circleK : ℝ) := by
    unfold CatalanMeasure.circleK; norm_num
  have hz : (CatalanMeasure.circleK : ℝ) ^ N ≤ Real.exp (110.475 * N) := by
    calc (CatalanMeasure.circleK : ℝ) ^ N ≤ Real.exp 110.475 ^ N :=
          pow_le_pow_left₀ hK0 circleK_le_exp N
      _ = Real.exp (110.475 * N) := by rw [← Real.exp_nat_mul]; ring_nf
  have hpow : fixedNodeCap N = Real.exp (-28 * Real.log 2 * N) := rfl
  have hN4 : (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2) ≤
      (8 * 48 * 65 ^ 3 * (16 * 10 ^ 8)) * Real.exp ((N : ℝ) / 50) := by
    have h100 : (N : ℝ) ≤ 200 * Real.exp ((N : ℝ) / 200) := by
      have := Real.add_one_le_exp ((N : ℝ) / 200 - 1)
      have h2 : Real.exp ((N : ℝ) / 200 - 1) ≤ Real.exp ((N : ℝ) / 200) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hq : (N : ℝ) ^ 4 ≤ (16 * 10 ^ 8) * Real.exp ((N : ℝ) / 50) := by
      have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      calc (N : ℝ) ^ 4 ≤ (200 * Real.exp ((N : ℝ) / 200)) ^ 4 := pow_le_pow_left₀ h0 h100 4
        _ = (16 * 10 ^ 8) * Real.exp ((N : ℝ) / 50) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
          ring_nf
    have he : (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2) = (8 * 48 * 65 ^ 3) * (N : ℝ) ^ 4 := by
      simp only [n, H, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [he]
    nlinarith [hq]
  have hbig : (8 * 48 * 65 ^ 3 * (16 * 10 ^ 8) : ℝ) ≤ Real.exp 40 := by
    have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have : Real.exp 40 = Real.exp 1 ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (8 * 48 * 65 ^ 3 * (16 * 10 ^ 8) : ℝ) ≤ (2.7 : ℝ) ^ 40 := by norm_num
      _ ≤ Real.exp 1 ^ 40 := pow_le_pow_left₀ (by norm_num) h2 40
  have hcR : (n N : ℝ) * separateEnergyCost ≤ 48 * N * (573 / 100) := by
    simp only [n, Nat.cast_mul, Nat.cast_ofNat]
    unfold separateEnergyCost
    norm_num
  calc (n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N) *
        (fixedNodeCap N * Real.exp ((n N : ℝ) * separateEnergyCost))
      = ((n N : ℝ) * (H N : ℝ) * (8 * (H N : ℝ) ^ 2)) * (CatalanMeasure.circleK : ℝ) ^ N *
          (fixedNodeCap N) * Real.exp ((n N : ℝ) * separateEnergyCost) := by ring
    _ ≤ ((8 * 48 * 65 ^ 3 * (16 * 10 ^ 8)) * Real.exp ((N : ℝ) / 50)) * Real.exp (110.475 * N) *
          Real.exp (-28 * Real.log 2 * N) * Real.exp (48 * N * (573 / 100)) := by
        rw [hpow]
        gcongr
    _ ≤ Real.exp 40 * Real.exp ((N : ℝ) / 50) * Real.exp (110.475 * N) *
          Real.exp (-28 * Real.log 2 * N) * Real.exp (48 * N * (573 / 100)) := by
        gcongr
    _ ≤ Real.exp (separateRho * N) := by
        simp only [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        unfold separateRho
        push_cast
        norm_num at hl
        nlinarith


theorem separate_perturbation :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(separateRho * N)) →
        |aeval x (deltaPoly N) - aeval catalan (deltaPoly N)| ≤
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  intro ε hε
  obtain ⟨N₁, hD⟩ := separate_atomMatrix_det_bound (d := ε / 4) (by positivity)
  obtain ⟨N₂, hpre⟩ := realDeterminantPrefactor_eventually_le_exp (d := ε / 8) (by positivity)
  have hfac := factorial_n_le_exp (c := ε / 16) (by positivity)
  have hlog2 : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ ε / 16 * (n N : ℝ) ^ 2 := by
    have htend : Tendsto (fun N : ℕ => ε / 16 * (n N : ℝ) ^ 2) atTop atTop := by
      have : (fun N : ℕ => ε / 16 * (n N : ℝ) ^ 2) =
          fun N : ℕ => (ε / 16 * 2304) * (N : ℝ) ^ 2 := by
        funext N
        simp only [n, Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [this]
      exact Tendsto.const_mul_atTop (by positivity)
        ((tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
    exact htend.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (max (max N₁ N₂) 4000), hfac, hlog2] with N hN hf hl2
  have hcap0 : 0 < fixedNodeCap N := Real.exp_pos _
  intro x hx
  have hN0 : 0 < N := by omega
  set δ := x - catalan with hδ
  set Bβ : ℝ := 8 * (H N : ℝ) ^ 2 * (CatalanMeasure.circleK : ℝ) ^ N with hBβ
  set c : ℝ := fixedNodeCap N * Real.exp ((n N : ℝ) * separateEnergyCost) with hc
  set M : ℝ := (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N *
    Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) with hM
  have hM0 : 0 ≤ M := by
    have := realDeterminantSheetPrefactor_nonneg N
    positivity
  have hc0 : 0 ≤ c := by positivity
  have hB0 : 0 ≤ Bβ := by
    have : (0 : ℝ) ≤ (CatalanMeasure.circleK : ℝ) := by unfold CatalanMeasure.circleK; norm_num
    positivity
  have hmain := CatalanMeasure.abs_det_add_atoms_sub_le (baseMatrix N) (atomVectors N)
    (fun a k => quadWeight N (quadNode (H N)) a k.val) δ hM0 hB0
    (fun a k => CatalanMeasure.quadWeight_chebNode_circle_le N a k.val) hc0 (hD N (by omega))
  rw [delta_matrix_eq hN0 x, aeval_catalan_deltaPoly hN0]
  change |_ - (baseMatrix N).det| ≤ _
  refine hmain.trans ?_
  -- the perturbation is small
  have hsmall : (n N : ℝ) * ((H N : ℝ) * (|δ| * Bβ * c)) ≤ 1 := by
    have hr := separate_rho_condition (N := N) (by omega)
    have hδe : |δ| * Real.exp (separateRho * N) ≤ 1 := by
      calc |δ| * Real.exp (separateRho * N) ≤ Real.exp (-(separateRho * N)) *
            Real.exp (separateRho * N) := mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h0 : 0 ≤ (n N : ℝ) * (H N : ℝ) * Bβ * c := by positivity
    calc (n N : ℝ) * ((H N : ℝ) * (|δ| * Bβ * c)) = |δ| * ((n N : ℝ) * (H N : ℝ) * Bβ * c) := by
          ring
      _ ≤ |δ| * Real.exp (separateRho * N) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ ≤ 1 := hδe
  have hpow := CatalanMeasure.one_add_pow_le_exp (t := (H N : ℝ) * (|δ| * Bβ * c))
    (by positivity) (n N)
  have he1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hfactor : (1 + (H N : ℝ) * (|δ| * Bβ * c)) ^ n N - 1 ≤ 2 := by
    have := Real.exp_le_exp.mpr hsmall
    linarith
  -- the prefactor
  have hfacn : (((n N) ! : ℕ) : ℝ) ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) := hf
  have hpref : (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N ≤
      Real.exp (ε / 8 * (n N : ℝ) ^ 2) * Real.exp (ε / 16 * (n N : ℝ) ^ 2) ^ 2 := by
    have hp := hpre N (by omega)
    unfold realDeterminantPrefactor at hp
    have hf0 : (0 : ℝ) < (((n N) ! : ℕ) : ℝ) := by positivity
    have heq : (2 : ℝ) ^ n N * realDeterminantSheetPrefactor N =
        ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N / (((n N) ! : ℕ) : ℝ) ^ 2) *
          (((n N) ! : ℕ) : ℝ) ^ 2 := by
      field_simp
    rw [heq]
    exact mul_le_mul hp (pow_le_pow_left₀ hf0.le hfacn 2) (by positivity) (Real.exp_pos _).le
  have h2 : (2 : ℝ) ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hl2
  calc M * ((1 + (H N : ℝ) * (|δ| * Bβ * c)) ^ n N - 1) ≤ M * 2 :=
        mul_le_mul_of_nonneg_left hfactor hM0
    _ ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) * ((2 : ℝ) ^ n N * realDeterminantSheetPrefactor N) *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) := by
        rw [hM]
        have := realDeterminantSheetPrefactor_nonneg N
        nlinarith [Real.exp_pos ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 +
          Real.log 2 / 2)), mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n N)) this]
    _ ≤ Real.exp (ε / 16 * (n N : ℝ) ^ 2) *
          (Real.exp (ε / 8 * (n N : ℝ) ^ 2) * Real.exp (ε / 16 * (n N : ℝ) ^ 2) ^ 2) *
          Real.exp ((n N : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + ε / 4 + Real.log 2 / 2)) := by
        gcongr
    _ = Real.exp ((n N : ℝ) ^ 2 *
          (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + (9 / 16) * ε)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        linarith


theorem separate_catalan_irrationalityMeasure_pnt {η ε c : ℝ} (hη0 : 0 < η)
    (hη : η < 2304 * measureGap) (hε : 0 < ε) (hc : 1 < c) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((1 + ε) * separateRho * max (((44 : ℕ) : ℝ) / η) (c / ε))) <
        |catalan - a / b| :=
  catalan_irrationalityMeasure_of_perturbation_pnt (by norm_num [separateRho]) hη0 hη hε hc
    separate_perturbation


theorem catalan_irrationalityMeasure_7364 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(7364 : ℝ)) < |catalan - a / b| := by
  have hε : (0 : ℝ) < 10001 / 191031 := by norm_num
  have hc : (1 : ℝ) < 10001 / 10000 := by norm_num
  filter_upwards [separate_catalan_irrationalityMeasure_pnt measureEta_pos measureEta_lt hε hc,
    eventually_ge_atTop 1] with b hb hb1 a
  refine lt_of_le_of_lt ?_ (hb a)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1)
  have hX := measureEta_ratio_le
  have hmax : max (((44 : ℕ) : ℝ) / measureEta) ((10001 / 10000) / (10001 / 191031)) = 191031 / 10000 := by
    rw [max_eq_right (by norm_num at hX ⊢; linarith)]
    norm_num
  rw [hmax]
  unfold separateRho
  norm_num


theorem separate_catalan_irrationalityMeasure {η : ℝ} (hη0 : 0 < η)
    (hη : η < 2304 * measureGap) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3 * separateRho * max (((44 : ℕ) : ℝ) / η) 4)) <
        |catalan - a / b| :=
  catalan_irrationalityMeasure_of_perturbation (by norm_num [separateRho]) hη0 hη
    separate_perturbation

theorem catalan_irrationalityMeasure_20993 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(20993 : ℝ)) < |catalan - a / b| := by
  filter_upwards [separate_catalan_irrationalityMeasure measureEta_pos measureEta_lt,
    eventually_ge_atTop 1] with b hb hb1 a
  refine lt_of_le_of_lt ?_ (hb a)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1)
  have hX := measureEta_ratio_le
  have hmax : max (((44 : ℕ) : ℝ) / measureEta) 4 ≤ 191031 / 10000 :=
    max_le hX (by norm_num)
  unfold separateRho
  nlinarith


end OAI.InternalCatalan
