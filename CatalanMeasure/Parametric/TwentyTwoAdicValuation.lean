module
public import CatalanMeasure.Parametric.TwentyTwoAdicNorm
public import OAI.NumberTheory.Catalan.Arithmetic.FinitePlacePartialAssembly
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

open Filter
open scoped Topology
theorem twentyDeterminantRat_two_adic_valuation_lower (z : ℚ) {N : ℕ} (hN : 0 < N)
    (hd : determinantRat twenty z N ≠ 0) :
    -(21 / 200 : ℝ) * (20*N : ℝ) ^ 2 - 2 * (20*N : ℝ) -
        (20*N : ℝ) * Real.logb 2 (8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2) ≤
      (padicValRat 2 (determinantRat twenty z N) : ℝ) := by
  have hd₂ : (determinantRat twenty z N : ℚ_[2]) ≠ 0 := by exact_mod_cast hd
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hH : 0 < (27*N : ℝ) := by positivity
  have hA : 0 < 8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2 := by positivity
  have hApow : (8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2) ^ (20*N) ≠ 0 :=
    ne_of_gt (pow_pos hA _)
  have hE : (2 : ℝ) ^ ((42 : ℝ) * (N : ℝ)^2 + 40*N) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hn : twenty.n N=20*N :=rfl
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (norm_pos_iff.mpr hd₂) (by simpa only [twenty_H,hn,Nat.cast_mul,Nat.cast_ofNat] using twentyDeterminantRat_two_adic_norm_le z hN)
  rw [Padic.norm_eq_zpow_neg_valuation hd₂, Padic.valuation_ratCast] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1),
    Real.logb_mul hApow hE, Real.logb_pow,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hl
  simp only [Int.cast_neg,Nat.cast_mul,Nat.cast_ofNat] at hl
  nlinarith only [hl]

theorem twenty_tendsto_twoAdic_log_error (z : ℚ) :
    Tendsto (fun N : ℕ =>
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2)) / (20*N : ℝ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ) / (20 * (N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, add_zero] using
      (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 20 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hs := (hi.const_mul
    ((2 + Real.logb 2 (8 * discrepancyNormFactor z * (27 : ℝ) ^ 2)) / 20)).add
      (hl.const_mul 2)
  simp only [mul_zero, add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hF : 0 < discrepancyNormFactor z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_discrepancyNormFactor z)
  have hconst : 8 * discrepancyNormFactor z * (27 : ℝ) ^ 2 ≠ 0 := by positivity
  have hfactor : 8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2 =
      (8 * discrepancyNormFactor z * (27 : ℝ) ^ 2) * (N : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hfactor, Real.logb_mul hconst (pow_ne_zero _ hNr), Real.logb_pow]
  push_cast
  field_simp [hNr]
  ring

theorem twentyDeterminantRat_two_adic_eventually_lower (z : ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinantRat twenty z N ≠ 0 →
      -(21 / 200 : ℝ) - ε ≤
        (padicValRat 2 (determinantRat twenty z N) : ℝ) / (20*N : ℝ) ^ 2 := by
  have he : ∀ᶠ N : ℕ in atTop,
      (2 + Real.logb 2 (8 * discrepancyNormFactor z * (27*N : ℝ) ^ 2)) / (20*N : ℝ) < ε :=
    (tendsto_order.mp (twenty_tendsto_twoAdic_log_error z)).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with N heN hN
  intro hd
  have hn : 0 < (20*N : ℝ) := by positivity
  have herr := mul_le_mul_of_nonneg_left
    (le_of_lt ((div_lt_iff₀ hn).mp heN)) (le_of_lt hn)
  have hv := twentyDeterminantRat_two_adic_valuation_lower z hN hd
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  nlinarith only [herr, hv]


end
end CatalanMeasure.Parametric
