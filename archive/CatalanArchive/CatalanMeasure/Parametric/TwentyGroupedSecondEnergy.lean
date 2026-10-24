module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyGroupedConstants
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPhysicalCertifiedFields
public import CatalanArchive.CatalanMeasure.Parametric.PublishedGroupedBudgets

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan TwentyCertified Set Filter
open scoped Topology BigOperators

noncomputable section

theorem twenty_log_reciprocal_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log 2 / (twenty.n N : ℝ) ≤ ε := by
  have ht : Tendsto (fun N : ℕ => Real.log 2 / (twenty.n N : ℝ)) atTop (𝓝 0) := by
    have hh := reciprocalScale_tendsto.const_mul (Real.log 2)
    convert hh using 1
    · funext N
      simp only [reciprocalScale, Parameters.n, twenty, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · ring
  exact ((tendsto_order.mp ht).2 ε hε).mono fun _ h => h.le

set_option maxHeartbeats 1600000 in
theorem twenty_grouped_second_energy_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = twenty.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedValueWithFields (twenty.n N : ℝ) (groupedPhysicalConstant twenty N r a b)
        (populationPhysicalFreeField twenty N) (groupedPhysicalMarkedField twenty N)
        (groupedPhysicalNearField twenty N) (populationPhysicalColumnField twenty N (a + b))
        z x y s ≤ -twentyDualTarget + Real.log 2 / 2 +
          (89 / 20 : ℝ) * (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  obtain ⟨e, he, herr⟩ := twenty_grouped_error_eventually p20 v20 (by linarith : 0 < δ / 2)
  filter_upwards [physical_row20_eventually hε, physical_column20_eventually hε,
      twenty_log_reciprocal_eventually hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hy hs hzi hxi hyi hsi
  let ν : ℝ := twenty.n N
  let α : ℝ := ((a + b : ℕ) : ℝ) / ν
  let β : ℝ := (b : ℝ) / ν
  have hν : 0 < ν := by
    dsimp only [ν]
    exact_mod_cast n_pos twenty_admissible hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / ν = 1 - α := by
    have hf := twenty_population_fractions hN (show r + (a + b) = twenty.n N by omega)
    dsimp only [α, ν]
    linarith only [hf]
  have hmarked : (a : ℝ) / ν = α - β := by
    dsimp only [α, β]
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound (constant := groupedPhysicalConstant twenty N r a b) hν he
    (by dsimp only [ν]; exact_mod_cast (show r + a ≤ twenty.n N by omega))
    (by dsimp only [ν]; exact_mod_cast (show b ≤ twenty.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    p20 p20 v20 p20_summable p20_summable v20_summable
    (populationPhysicalFreeField twenty N) (groupedPhysicalMarkedField twenty N)
    (groupedPhysicalNearField twenty N) (populationPhysicalColumnField twenty N (a + b))
    ((CatalanMeasure.TwentyTrial.K2A0.MX : ℝ) + ε) ((2 / 25 : ℝ) + ε)
    (-(63 / 100 : ℝ) + ε) ((CatalanMeasure.TwentyTrial.K2A0.MY : ℝ) + ε + α * Real.log 2)
    (fun i => by
      have hz' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
        by_cases ht : z i < 0
        · exact Or.inl ⟨(hz i).1.le, ht⟩
        · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm (hz0 i)), (hz i).2⟩
      have hh := hrow (z i) hz'
      linarith only [hh])
    (fun i => by
      have hh := twenty_grouped_marked_field_bound hN ⟨(hx i).1.le, (hx i).2.le⟩
      linarith only [hh, hsmall])
    (fun i => by
      have hh := twenty_grouped_near_field_bound hN (hy i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := hcol (s i) (hs i)
      have hl : Real.log (1 + s i) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [(hs i).1]) (by linarith [(hs i).2])
      have hm := mul_le_mul_of_nonneg_left hl hα
      have hid : populationPhysicalColumnField twenty N (a + b) (s i) =
          populationEndpointColumnField twenty N 0 (s i) + α * Real.log (1 + s i) := by
        unfold populationPhysicalColumnField populationEndpointColumnField α ν
        ring
      rw [hid]
      linarith only [hh, hm])
  have hconst := twenty_grouped_constant_le hN hcount
  have hbudget := published_second_grouped_budget hα hβ
  have hnorm := norm20_bound
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) fieldSum20
  have hεα := mul_nonneg hε.le hα
  have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  rw [← hnu] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  dsimp only [α, β, ν, ε] at hb hconst hbudget hfields hεα ⊢
  ring_nf at hb hconst hbudget hfields hnorm herror hεα ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα]

end

end CatalanMeasure.Parametric
