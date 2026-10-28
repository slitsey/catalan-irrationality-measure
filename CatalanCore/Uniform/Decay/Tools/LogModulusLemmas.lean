module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
@[expose] public section

/-!
# Building blocks for the segment log-modulus bound

(a) `abs_log_sub_log_le`: `|log a - log b| ≤ |a - b| / min a b`.
(b) `integral_abs_log_shift`: `∫_{c-r}^{c+r} |log (s - c)| ds = 2 (r - r log r)` for `0 ≤ r ≤ 1`.
(c) `integral_inv_le_log`: `∫_α^β du/u ≤ log (1 + ℓ/α)` when `0 < α ≤ β ≤ α + ℓ`.
-/

namespace CatalanCore.Uniform.Decay.Tools

open intervalIntegral

theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  wlog hba : b ≤ a generalizing a b
  · have := this hb ha (le_of_not_ge hba)
    rw [abs_sub_comm (Real.log a) (Real.log b), abs_sub_comm a b, min_comm]
    exact this
  rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.2 hba)]
  have h0 : 0 ≤ Real.log a - Real.log b := sub_nonneg.2 (Real.log_le_log hb hba)
  rw [abs_of_nonneg h0, ← Real.log_div ha.ne' hb.ne']
  have := Real.log_le_sub_one_of_pos (div_pos ha hb)
  calc Real.log (a / b) ≤ a / b - 1 := this
    _ = (a - b) / b := by field_simp

theorem integral_abs_log_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ u in (0 : ℝ)..r, |Real.log u| = r - r * Real.log r := by
  have : ∫ u in (0 : ℝ)..r, |Real.log u| = ∫ u in (0 : ℝ)..r, -Real.log u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hr0] at hu
    rcases hu.1.eq_or_lt with h | h
    · rw [← h]; simp
    · exact abs_of_nonpos (Real.log_nonpos h.le (hu.2.trans hr1))
  rw [this, intervalIntegral.integral_neg, integral_log]
  simp

theorem integral_abs_log_symm (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ u in (-r)..r, |Real.log u| = 2 * (r - r * Real.log r) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => |Real.log u|) MeasureTheory.volume a b :=
    fun a b => (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-r) 0) (hint 0 r),
    integral_abs_log_zero r hr0 hr1]
  have h2 : ∫ u in (-r)..(0 : ℝ), |Real.log u| = ∫ u in (0 : ℝ)..r, |Real.log (-u)| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := r) (fun u : ℝ => |Real.log u|)
    simp only [neg_zero] at this
    exact this.symm
  rw [h2]
  simp_rw [Real.log_neg_eq_log]
  rw [integral_abs_log_zero r hr0 hr1]
  ring

theorem integral_abs_log_shift (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∫ s in (c - r)..(c + r), |Real.log (s - c)| = 2 * (r - r * Real.log r) := by
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => |Real.log u|) c]
  simp only [sub_sub_cancel_left, add_sub_cancel_left]
  exact integral_abs_log_symm r hr0 hr1

theorem integral_inv_le_log {α β ℓ : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ α + ℓ) :
    ∫ u in α..β, u⁻¹ ≤ Real.log (1 + ℓ / α) := by
  rw [integral_inv_of_pos hα (hα.trans_le hαβ)]
  apply Real.log_le_log (div_pos (hα.trans_le hαβ) hα)
  rw [div_le_iff₀ hα]
  have : (1 + ℓ / α) * α = α + ℓ := by field_simp
  linarith

end CatalanCore.Uniform.Decay.Tools
