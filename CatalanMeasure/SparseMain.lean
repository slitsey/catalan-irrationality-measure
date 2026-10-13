module
public import CatalanMeasure.SquareMain
public import CatalanMeasure.SparseDenominatorGrowth
@[expose] public section
open Polynomial Filter Real
open scoped Topology BigOperators Nat
namespace OAI.InternalCatalan

noncomputable def sparseMeasureGap : ℝ :=measureGap+1999/1152000

theorem sparseMeasureGap_pos : 0<sparseMeasureGap :=by
  have hh :=measureGap_pos
  unfold sparseMeasureGap
  linarith

theorem sparse_eta_lt : (63/10:ℝ)<2304*sparseMeasureGap :=by
  have hh :=measureEta_lt
  unfold measureEta at hh
  unfold sparseMeasureGap
  linarith

theorem natDegree_sparse_denom_mul_deltaPoly_le (p : ℕ) :
    (C (sparseDenomBound p : ℚ) * deltaPoly p).natDegree ≤ 44 * p :=
  (natDegree_C_mul_le _ _).trans (natDegree_deltaPoly_le_44 p)

theorem sparse_denom_mul_deltaPoly_int_values {p : ℕ} (hp : 0 < p) (i : ℕ) :
    ∃ m : ℤ, (C (sparseDenomBound p : ℚ) * deltaPoly p).eval (i : ℚ) = m := by
  rw [eval_mul, eval_C, eval_deltaPoly]
  exact exists_int_sparseDenomBound_mul hp i

/-- The integer polynomial `Q_p = (44 p)! · D_p · Δ_p` (and `0` for `p = 0`). -/
noncomputable def sparseMeasureIntPoly (p : ℕ) : ℤ[X] :=
  if hp : 0 < p then
    Classical.choose (CatalanMeasure.exists_int_poly_factorial_mul
      (C (sparseDenomBound p : ℚ) * deltaPoly p) (natDegree_sparse_denom_mul_deltaPoly_le p)
      (sparse_denom_mul_deltaPoly_int_values hp))
  else 0

theorem sparseMeasureIntPoly_spec {p : ℕ} (hp : 0 < p) :
    (sparseMeasureIntPoly p).map (Int.castRingHom ℚ) =
        C (((44 * p) ! : ℕ) : ℚ) * (C (sparseDenomBound p : ℚ) * deltaPoly p) ∧
      (sparseMeasureIntPoly p).natDegree ≤ 44 * p := by
  unfold sparseMeasureIntPoly
  rw [dif_pos hp]
  exact Classical.choose_spec (CatalanMeasure.exists_int_poly_factorial_mul
    (C (sparseDenomBound p : ℚ) * deltaPoly p) (natDegree_sparse_denom_mul_deltaPoly_le p)
    (sparse_denom_mul_deltaPoly_int_values hp))

theorem sparseMeasureIntPoly_natDegree_le (p : ℕ) : (sparseMeasureIntPoly p).natDegree ≤ 44 * p := by
  by_cases hp : 0 < p
  · exact (sparseMeasureIntPoly_spec hp).2
  · unfold sparseMeasureIntPoly
    rw [dif_neg hp]
    simp

theorem aeval_sparseMeasureIntPoly {p : ℕ} (hp : 0 < p) (x : ℝ) :
    aeval x (sparseMeasureIntPoly p) = ((44 * p) ! : ℝ) * (sparseDenomBound p : ℝ) * aeval x (deltaPoly p) := by
  rw [← aeval_map_algebraMap ℚ x (sparseMeasureIntPoly p), algebraMap_int_eq,
    (sparseMeasureIntPoly_spec hp).1]
  simp only [map_mul, aeval_C, eq_ratCast, Rat.cast_natCast]
  try ring

theorem sparseMeasureIntPoly_hypotheses {ρ η : ℝ} (hη : η < 2304 * sparseMeasureGap)
    (hpert : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + ε))) :
    ∃ P₀ : ℕ,
      (∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
        aeval ((a : ℝ) / b) (sparseMeasureIntPoly p) ≠ 0) ∧
      (∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ, |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (sparseMeasureIntPoly p)| ≤ Real.exp (-(η * (p : ℝ) ^ 2))) := by
  set γ := sparseMeasureGap with hγ
  have hγ0 : 0 < γ := sparseMeasureGap_pos
  set e : ℝ := (2304 * γ - η) / 9216 with he
  have he0 : 0 < e := by rw [he]; linarith
  -- eventual estimates, all at the prime index `p`
  have hev : ∀ᶠ p : ℕ in atTop,
      (∀ x : ℝ, |x - catalan| ≤ Real.exp (-(ρ * p)) →
        |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| ≤
          Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e))) ∧
      |determinant p| ≤
        Real.exp ((n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e)) ∧
      Real.log (sparseDenomBound p) ≤ (8609 / 4608 + 505 / 4608 * Real.log 2 - 1999 / 1152000 + e) * (n p : ℝ) ^ 2 ∧
      (((n p) ! : ℕ) : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) ∧
      Real.log 2 ≤ e * (n p : ℝ) ^ 2 ∧
      fixedDeterminantPrimeCutoff < p ∧ 0 < p := by
    have hlog2 : ∀ᶠ p : ℕ in atTop, Real.log 2 ≤ e * (n p : ℝ) ^ 2 := by
      have htend : Tendsto (fun p : ℕ => e * (n p : ℝ) ^ 2) atTop atTop := by
        have : (fun p : ℕ => e * (n p : ℝ) ^ 2) = fun p : ℕ => (e * 2304) * (p : ℝ) ^ 2 := by
          funext p
          simp only [n, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [this]
        exact Tendsto.const_mul_atTop (by nlinarith [he0])
          ((tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop)
      exact htend.eventually (eventually_ge_atTop _)
    filter_upwards [hpert (e) he0,
      eventually_realDeterminant_abs_upper_dual (ε := e) he0,
      log_sparseDenomBound_eventually_le (ε := e) he0,
      factorial_n_le_exp (c := e) he0, hlog2,
      eventually_gt_atTop fixedDeterminantPrimeCutoff, eventually_gt_atTop 0]
      with p h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hev
  refine ⟨P₀, ?_, ?_⟩
  · -- arithmetic nonvanishing
    intro p hp hprime a b hb hpb
    haveI : Fact p.Prime := ⟨hprime⟩
    obtain ⟨-, -, -, -, -, hcut, hp0⟩ := hP₀ p hp
    rw [aeval_sparseMeasureIntPoly hp0]
    have hx : ((a : ℝ) / b) = (((a : ℚ) / b : ℚ) : ℝ) := by
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [hx, aeval_ratCast_eq, eval_deltaPoly]
    have hdet := determinantRat_div_ne_zero_of_not_square_dvd hcut a hb hpb
    have hfac : (((44 * p) ! : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hM : (sparseDenomBound p : ℝ) ≠ 0 := by exact_mod_cast sparseDenomBound_ne_zero p
    have hdetR : ((determinantRat ((a : ℚ) / b) p : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hdet
    exact mul_ne_zero (mul_ne_zero hfac hM) hdetR
  · -- smallness near `G`
    intro p hp hprime x hx
    obtain ⟨hpert', hG, hM, hfacn, hlog2, -, hp0⟩ := hP₀ p hp
    have hfac : (((44 * p) ! : ℕ) : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) := by
      refine le_trans ?_ hfacn
      exact_mod_cast Nat.factorial_le (by unfold n; omega)
    rw [aeval_sparseMeasureIntPoly hp0]
    set E : ℝ := (n p : ℝ) ^ 2 * (-(229180925 / 100000000 : ℝ) + Real.log 2 / 2 + e)
      with hE
    have hΔ : |aeval x (deltaPoly p)| ≤ 2 * Real.exp E := by
      have h1 := hpert' x hx
      have h2 : aeval catalan (deltaPoly p) = determinant p := aeval_catalan_deltaPoly hp0
      calc |aeval x (deltaPoly p)|
          = |(aeval x (deltaPoly p) - aeval catalan (deltaPoly p)) +
              aeval catalan (deltaPoly p)| := by rw [sub_add_cancel]
        _ ≤ |aeval x (deltaPoly p) - aeval catalan (deltaPoly p)| +
              |aeval catalan (deltaPoly p)| := abs_add_le _ _
        _ ≤ Real.exp E + Real.exp E := add_le_add h1 (by rw [h2]; exact hG)
        _ = 2 * Real.exp E := by ring
    have hM' : (sparseDenomBound p : ℝ) ≤
        Real.exp ((8609 / 4608 + 505 / 4608 * Real.log 2 - 1999 / 1152000 + e) * (n p : ℝ) ^ 2) := by
      have hMpos : (0 : ℝ) < sparseDenomBound p := by
        exact_mod_cast Nat.pos_of_ne_zero (sparseDenomBound_ne_zero p)
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr hM
    have h2 : (2 : ℝ) ≤ Real.exp (e * (n p : ℝ) ^ 2) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hlog2
    have hfac0 : (0 : ℝ) ≤ (((44 * p) ! : ℕ) : ℝ) := by positivity
    have hM0 : (0 : ℝ) ≤ (sparseDenomBound p : ℝ) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hM0]
    calc (((44 * p) ! : ℕ) : ℝ) * (sparseDenomBound p : ℝ) * |aeval x (deltaPoly p)|
        ≤ Real.exp (e * (n p : ℝ) ^ 2) *
            Real.exp ((8609 / 4608 + 505 / 4608 * Real.log 2 - 1999 / 1152000 + e) * (n p : ℝ) ^ 2) *
            (Real.exp (e * (n p : ℝ) ^ 2) * Real.exp E) := by
          have hΔ' : |aeval x (deltaPoly p)| ≤
              Real.exp (e * (n p : ℝ) ^ 2) * Real.exp E :=
            hΔ.trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)
          gcongr
      _ = Real.exp (-(η / 2304) * (n p : ℝ) ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE]
          congr 1
          rw [he, hγ]
          unfold sparseMeasureGap measureGap
          ring
      _ = Real.exp (-(η * (p : ℝ) ^ 2)) := by
          congr 1
          simp only [n, Nat.cast_mul, Nat.cast_ofNat]
          ring


theorem catalan_irrationalityMeasure_2742 :
    ∀ᶠ b : ℕ in atTop,∀ a : ℤ,(b:ℝ)^(-(2742:ℝ)) < |catalan-a/b| :=by
  obtain ⟨P₀,hnz,hsmall⟩ :=sparseMeasureIntPoly_hypotheses sparse_eta_lt separate_perturbation
  have hh :=CatalanMeasure.irrationality_measure_of_polynomials_square_pnt
    catalan 44 (by norm_num : (0:ℝ)<63/10) (by norm_num [separateRho] : 0<separateRho)
    (by norm_num : (0:ℝ)<630063/8800000) (by norm_num : (1:ℝ)<10001/10000)
    sparseMeasureIntPoly P₀ sparseMeasureIntPoly_natDegree_le hnz hsmall
  filter_upwards [hh,eventually_ge_atTop (1:ℕ)] with b hb hb1 a
  refine lt_of_le_of_lt ?_ (hb a)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1)
  norm_num [separateRho]

theorem catalan_irrationalityMeasure_7675 :
    ∀ᶠ b : ℕ in atTop,∀ a : ℤ,(b:ℝ)^(-(7675:ℝ)) < |catalan-a/b| :=by
  obtain ⟨P₀,hnz,hsmall⟩ :=sparseMeasureIntPoly_hypotheses sparse_eta_lt separate_perturbation
  have hnz' : ∀ p,P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),0<b → ¬p∣b →
      aeval ((a:ℝ)/b) (sparseMeasureIntPoly p)≠0 :=by
    intro p hp hprime a b hb hpb
    apply hnz p hp hprime a b hb
    intro hsq
    exact hpb (dvd_trans (dvd_pow_self p (by decide : 2≠0)) hsq)
  have hh :=CatalanMeasure.irrationality_measure_of_polynomials catalan 44
    (by norm_num : (0:ℝ)<63/10) (by norm_num [separateRho] : 0<separateRho)
    sparseMeasureIntPoly P₀ sparseMeasureIntPoly_natDegree_le hnz' hsmall
  filter_upwards [hh,eventually_ge_atTop (1:ℕ)] with b hb hb1 a
  refine lt_of_le_of_lt ?_ (hb a)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1)
  norm_num [separateRho]

end OAI.InternalCatalan
