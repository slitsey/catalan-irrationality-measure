module
public import CatalanArchive.CatalanMeasure.Parametric.TargetFirstEnergy
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan TwentyCertified Set Filter Finset
open scoped Topology BigOperators
noncomputable section

/-- A complete first-population trial, including its physical finite corrections.
The p sequence is the physical sequence (twice the saved P sequence). -/
structure FirstTrialBoundsAt (target cost : ℝ) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  lambda : ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  lambda_nonneg : 0 ≤ lambda
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : barrierTrialNormSq p+barrierTrialNormSq v/2 ≤ normCap
  field_sum : MX+MY=fieldCap
  row : ∀ {ε : ℝ}, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalOneFreeField twenty N x+lambda*paramCaseField twenty N x-
        2*barrierTrialT p x-barrierTrialS v x-
        Real.log (1-x)/(2*(twenty.n N:ℝ)) ≤ MX+ε
  column : ∀ {ε : ℝ}, 0<ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0:ℝ) 1,
      populationEndpointColumnField twenty N 0 s+2*barrierTrialT v s-
        Real.log (1-s)/(twenty.n N:ℝ) ≤ MY+ε
  budget : ∀ a : ℝ,
    (-(1/5:ℝ)+(8/5)*a-a^2)*Real.log 2+
      normCap+(1-a)*fieldCap+a*(1-a)*Real.log 2+
      a*(lambda/5)+(9/10)*a ≤
        -target+Real.log 2/2+(cost+9/10)*a

set_option maxHeartbeats 1600000 in
theorem first_energy_with_trial {target c : ℝ} (D : FirstTrialBoundsAt target c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-(1 : ℝ) < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N (((m : ℝ) / (twenty.n N : ℝ))) x y s ≤
        -target + Real.log 2 / 2 + c * ((m : ℝ) / (twenty.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hlambda := D.lambda_nonneg
  obtain ⟨e, he, herr⟩ := twentyFirstDampingError_eventually D.lambda D.p D.v hε
  filter_upwards [D.row hε, D.column hε,
      twenty_log_reciprocal_eventually hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  let ν : ℝ := twenty.n N
  let α : ℝ := (m : ℝ) / ν
  have hν : 0 < ν := by dsimp only [ν]; exact_mod_cast n_pos twenty_admissible hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (p : ℝ) / ν = 1 - α := by
    have hh := twenty_population_fractions hN hpm
    dsimp only [α, ν]
    linarith only [hh]
  have hbound := free_population_fields_dual_bound
    (constant := populationPhysicalOneConstant twenty N p) hν he hlambda
    (by dsimp only [ν]; exact_mod_cast (show p ≤ twenty.n N by omega))
    (populationPhysicalOneFreeField twenty N)
    (fun u => populationPhysicalOneFixedField twenty N u - populationCommonLog twenty N u / ν)
    (populationEndpointColumnField twenty N α) (paramCaseField twenty N)
    x y s hx hs hxi hsi hcase D.p D.v D.p_summable D.v_summable
    D.norm_le
    (fun i => hrow (x i) (population_row_domain (hx i) (hx0 i)))
    (fun j => by
      have hc := twenty_marked_first_field_after_common hN (hy j) (hy0 j) hlambda
      have hsq : y j ^ 2 ≤ 1 := by nlinarith only [(hy j).1, (hy j).2]
      have hl : Real.log (1 + y j ^ 2) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by linarith only [hsq])
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hcorr := div_le_div_of_nonneg_right (show Real.log (1 + y j ^ 2) ≤ 2 * Real.log 2 by
        linarith only [hl, hl2]) (show (0 : ℝ) ≤ 2 * ν by positivity)
      have heq : 2 * Real.log 2 / (2 * ν) = Real.log 2 / ν := by ring
      rw [heq] at hcorr
      change populationPhysicalOneFixedField twenty N (y j) - populationCommonLog twenty N (y j) / ν +
        D.lambda * paramCaseField twenty N (y j) ≤
          -(2 / 5 : ℝ) * Real.log 2 + D.lambda / 5 + ε
      unfold populationPhysicalOneFixedField populationCommonLog
      dsimp only [ν] at hcorr ⊢
      ring_nf at hc hcorr hsmall ⊢
      linarith only [hc, hcorr, hsmall])
    (fun j => by
      have hc := hcol (s j) (hs j)
      have hl : Real.log (1 + s j) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [(hs j).1]) (by linarith [(hs j).2])
      have hm := mul_le_mul_of_nonneg_left hl hα
      have hid : populationEndpointColumnField twenty N α (s j) =
          populationEndpointColumnField twenty N 0 (s j) + α * Real.log (1 + s j) := by
        unfold populationEndpointColumnField
        ring
      rw [hid]
      exact (by linarith only [hc, hm] :
        populationEndpointColumnField twenty N 0 (s j) + α * Real.log (1 + s j) +
          2 * barrierTrialT D.v (s j) - Real.log (1 - s j) / ν ≤
            D.MY + ε + α * Real.log 2))
  have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hbound' : weightedPopulationOneValue twenty N α x y s ≤
      populationPhysicalOneConstant twenty N p - (3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      D.normCap + ((p : ℝ) / ν) * (D.MX + ε +
        (D.MY + ε + α * Real.log 2)) +
      α * (-(2 / 5 : ℝ) * Real.log 2 + D.lambda / 5 + ε) +
      twentyFirstDampingError D.lambda e D.p D.v N := by
    unfold weightedPopulationOneValue
    convert hbound using 1
    unfold twentyFirstDampingError α
    dsimp only [ν]
    rw [hnu]
    ring
  have hconst := twenty_physical_one_constant_le hN hpm
  have hbudget := D.budget α
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [hfree] at hbound' hconst
  dsimp only [α, ν, ε] at hbound' hconst hbudget hfields hεα herror ⊢
  ring_nf at hbound' hconst hbudget hfields herror hεα ⊢
  nlinarith only [hbound', hconst, hbudget, hfields, herror, hεα, hδ]

theorem first_marked_product_with_trial {target c : ℝ} (D : FirstTrialBoundsAt target c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      firstMarkedProduct twenty N hpm x y s ≤
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          (20 * c) * N * m) := by
  filter_upwards [first_energy_with_trial D hε, eventually_gt_atTop (0 : ℕ)]
    with N he hN p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx j) (fun j => by simpa using hy j) i
  have hz0 : ∀ i, Fin.append x y i ≠ 0 := by
    intro i
    exact Fin.addCases (fun j => by simpa using hx0 j) (fun j => by simpa using hy0 j) i
  have hp := populationOneProduct_pos twenty_admissible hN hpm x y s hz hz0 hs hxi hsi
  have hc : ∀ j, 0 < |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| := by
    intro j
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of twenty N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hcp : 0 < ∏ j, |(rowCommonFactor twenty N).eval (realCoordinateInv (y j))| :=
    prod_pos fun j _ => hc j
  have hlog := log_populationOneProduct_weighted twenty_admissible hN hpm
    x y s hz hz0 hs hxi hsi
  have hval := he p m hpm x y s hx hx0 hy hy0 hs hxi hsi hcase
  have hn : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hn0 : (20 : ℝ) * N ≠ 0 := by positivity
  have hid : (twenty.n N : ℝ) ^ 2 *
      (-target + Real.log 2 / 2 + c * ((m : ℝ) / twenty.n N) + ε) =
      (20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + (20 * c) * N * m := by
    rw [hn]
    field_simp [hn0]
    ring
  have hbound := mul_le_mul_of_nonneg_left hval (sq_nonneg (twenty.n N : ℝ))
  rw [← hlog, hid] at hbound
  rw [firstMarkedProduct, ← Real.exp_log (div_pos hp hcp)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div hp.ne' hcp.ne', Real.log_prod (fun j _ => (hc j).ne')]
  exact hbound


end
end CatalanMeasure.Parametric
