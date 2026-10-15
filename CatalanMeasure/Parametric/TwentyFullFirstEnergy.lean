module

public import CatalanMeasure.Parametric.TwentyGroupedSecondEnergy
public import CatalanMeasure.Parametric.TwentyEndpointControl

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan TwentyCertified Set Filter
open scoped Topology BigOperators

noncomputable section

set_option maxHeartbeats 1600000 in
theorem twenty_full_first_energy_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-(1 : ℝ) < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N (((m : ℝ) / (twenty.n N : ℝ))) x y s ≤
        -twentyDualTarget + Real.log 2 / 2 + (9 / 2 : ℝ) * ((m : ℝ) / (twenty.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hlambda : (0 : ℝ) ≤ lambda10 := by norm_num [lambda10]
  obtain ⟨e, he, herr⟩ := twentyFirstDampingError_eventually (lambda10 : ℝ) p10 v10 hε
  filter_upwards [physical_row10_eventually hε, physical_column10_eventually hε,
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
    x y s hx hs hxi hsi hcase p10 v10 p10_summable v10_summable
    (by simpa only [one_mul] using norm10_bound)
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
        (lambda10 : ℝ) * paramCaseField twenty N (y j) ≤
          -(2 / 5 : ℝ) * Real.log 2 + (lambda10 : ℝ) / 5 + ε
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
          2 * barrierTrialT v10 (s j) - Real.log (1 - s j) / ν ≤
            (CatalanMeasure.TwentyTrial.K1A0.MY : ℝ) + ε + α * Real.log 2))
  have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  have hbound' : weightedPopulationOneValue twenty N α x y s ≤
      populationPhysicalOneConstant twenty N p - (3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 +
      twentyNorm10 + ((p : ℝ) / ν) * ((CatalanMeasure.TwentyTrial.K1A0.MX : ℝ) + ε +
        ((CatalanMeasure.TwentyTrial.K1A0.MY : ℝ) + ε + α * Real.log 2)) +
      α * (-(2 / 5 : ℝ) * Real.log 2 + (lambda10 : ℝ) / 5 + ε) +
      twentyFirstDampingError (lambda10 : ℝ) e p10 v10 N := by
    unfold weightedPopulationOneValue
    convert hbound using 1
    unfold twentyFirstDampingError α
    dsimp only [ν]
    rw [hnu]
    ring
  have hconst := twenty_physical_one_constant_le hN hpm
  have hbudget := published_first_full_interval_budget α
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) fieldSum10
  have hεα := mul_nonneg hε.le hα
  rw [hfree] at hbound' hconst
  dsimp only [α, ν, ε] at hbound' hconst hbudget hfields hεα herror ⊢
  norm_num only [lambda10, Rat.cast_div, Rat.cast_ofNat] at hbound' herror
  ring_nf at hbound' hconst hbudget hfields herror hεα ⊢
  nlinarith only [hbound', hconst, hbudget, hfields, herror, hεα, hδ]

end

end CatalanMeasure.Parametric
