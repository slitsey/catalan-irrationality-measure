module

public import CatalanArchive.CatalanMeasure.Parametric.GroupedPhysicalProduct
public import CatalanArchive.CatalanMeasure.Parametric.TwentyRegularization

/-!
# Uniform physical field caps and grouped regularization errors
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Set Filter
open scoped Topology BigOperators

noncomputable section

theorem twenty_grouped_marked_field_identity {N : ℕ} (hN : 0 < N) (x : ℝ) :
    groupedPhysicalMarkedField twenty N x =
      -(9 / 10 : ℝ) * Real.log (1 + x ^ 2) + Real.log (1 + x ^ 2) / (twenty.n N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : twenty.n N - twenty.g N - 1 = 18 * N - 1 := by
    change 20 * N - 2 * N - 1 = 18 * N - 1
    omega
  unfold groupedPhysicalMarkedField
  rw [he, Nat.cast_sub (by omega : 1 ≤ 18 * N)]
  simp only [Parameters.n, twenty, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

theorem twenty_grouped_marked_field_bound {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    groupedPhysicalMarkedField twenty N x - 2 * barrierTrialT TwentyCertified.p20 x ≤
      (2 / 25 : ℝ) + Real.log 2 / (twenty.n N : ℝ) := by
  have hn : (0 : ℝ) < twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
  have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
  have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith only [hsq])
  have hcorr := div_le_div_of_nonneg_right hlog hn.le
  have hb := TwentyCertified.grouped_marked_field_bound hx
  rw [twenty_grouped_marked_field_identity hN]
  linarith only [hb, hcorr]

theorem twenty_grouped_near_field_bound {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    groupedPhysicalNearField twenty N y - TwentyCertified.p20 1 * y ≤
      -(63 / 100 : ℝ) + Real.log 2 / (twenty.n N : ℝ) := by
  have hn : (0 : ℝ) < twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
  have hsq : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
  have hlog : Real.log (1 + y ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith only [hsq])
  have hcorr := div_le_div_of_nonneg_right hlog hn.le
  have hb := twenty_finite_near_field_bound hN hy
  have he : twenty.n N - 1 - 2 * twenty.g N = 16 * N - 1 := by
    change 20 * N - 1 - 2 * (2 * N) = 16 * N - 1
    omega
  unfold groupedPhysicalNearField
  rw [twenty_grouped_marked_field_identity hN, he, abs_of_pos hy.1]
  have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  rw [← hnu] at hb
  linarith only [hb, hcorr]

theorem twenty_grouped_error_tendsto (e : ℝ) (pp v : ℕ → ℝ) :
    Tendsto (fun N : ℕ => groupedPopulationError (20 * N) e pp pp v) atTop
      (𝓝 (e * (4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20))) := by
  have hh := twenty_reciprocal_three_term_tendsto
    ((3 / 2 : ℝ) * (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)))
    (Real.log 2 - Real.log e) (Real.log 2 - 2 * Real.log e)
    (e * (4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20))
  convert hh using 1
  funext N
  unfold groupedPopulationError coupledCosineError freePopulationRegularizationError
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem twenty_grouped_error_eventually (pp v : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : ℝ, e ∈ Ioo (0 : ℝ) (1 / 8) ∧
      ∀ᶠ N : ℕ in atTop, groupedPopulationError (20 * N) e pp pp v ≤ δ := by
  have hp : 0 ≤ ∑' j, |pp j| := tsum_nonneg (fun j => abs_nonneg _)
  have hv : 0 ≤ ∑' j, |v j| := tsum_nonneg (fun j => abs_nonneg _)
  have hp1 : 0 ≤ |pp 1| := abs_nonneg _
  obtain ⟨e, he, hec⟩ := exists_small_population_damping
    (by linarith only [hp, hv, hp1] : (0 : ℝ) ≤
      4 * (∑' j, |pp j|) + 4 * (∑' j, |v j|) + |pp 1| + 20) hδ
  refine ⟨e, he, ?_⟩
  exact ((tendsto_order.mp (twenty_grouped_error_tendsto e pp v)).2 δ hec).mono
    (fun _ h => h.le)

end

end CatalanMeasure.Parametric
