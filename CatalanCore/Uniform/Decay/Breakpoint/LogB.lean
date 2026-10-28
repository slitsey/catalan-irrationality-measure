import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
set_option Elab.async false

/-!
# `s^m |log s|` is increasing on `(0, 1/3]` (lane D, package D14)

`pow_mul_abs_log_le`: for `m ≥ 1` and `0 < s ≤ S ≤ 1/3`, `s^m |log s| ≤ S^m |log S|`.  This bounds the
logarithmic terms `b_m s^m ln s` of the breakpoint expansion on a whole interval `(0, S]` by their
value at the right end.  `abs_log_le_of_pow` bounds `|log S|` by a checked binary exponent.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

theorem log_three_ge_one : (1 : ℝ) ≤ Real.log 3 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact ((Real.lt_log_iff_exp_lt (by norm_num)).2 h).le

theorem log_le_neg_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 3) : Real.log x ≤ -1 := by
  have h1 : Real.log x ≤ Real.log (1 / 3) := Real.log_le_log hx0 hx
  have h2 : Real.log (1 / 3) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  linarith [log_three_ge_one]

theorem pow_mul_abs_log_le {m : ℕ} (hm : 1 ≤ m) {s S : ℝ} (hs0 : 0 < s) (hs : s ≤ S)
    (hS : S ≤ 1 / 3) : s ^ m * |Real.log s| ≤ S ^ m * |Real.log S| := by
  have hS0 : 0 < S := lt_of_lt_of_le hs0 hs
  have hlS : Real.log S ≤ -1 := log_le_neg_one hS0 hS
  have hls : Real.log s ≤ -1 := log_le_neg_one hs0 (hs.trans hS)
  rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
  set τ := s / S with hτdef
  have hτ0 : 0 < τ := div_pos hs0 hS0
  have hτ1 : τ ≤ 1 := (div_le_one hS0).2 hs
  have hsτ : s = S * τ := by rw [hτdef]; field_simp
  have hlog : Real.log s = Real.log S + Real.log τ := by
    rw [hsτ, Real.log_mul hS0.ne' hτ0.ne']
  have hlτ : Real.log τ ≥ 1 - 1 / τ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hτ0)
    rw [Real.log_inv] at this
    have h1 : (1 : ℝ) - 1 / τ = 1 - τ⁻¹ := by rw [one_div]
    linarith
  -- τ^m (-log τ) ≤ 1 - τ^m
  have hpm : 0 < τ ^ m := pow_pos hτ0 m
  have hpm1 : τ ^ m ≤ 1 := pow_le_one₀ hτ0.le hτ1
  have hkey : τ ^ m * (-Real.log τ) ≤ 1 - τ ^ m := by
    have h1 : τ ^ m * (-Real.log τ) ≤ τ ^ m * (1 / τ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hpm.le
    have h2 : τ ^ m * (1 / τ - 1) = τ ^ (m - 1) - τ ^ m := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
    have h3 : τ ^ (m - 1) ≤ 1 := pow_le_one₀ hτ0.le hτ1
    linarith
  have hSm : 0 < S ^ m := pow_pos hS0 m
  have hL : (1 : ℝ) ≤ -Real.log S := by linarith
  have h4 : τ ^ m * (-Real.log S) + τ ^ m * (-Real.log τ) ≤ -Real.log S := by
    nlinarith [hkey, mul_nonneg (sub_nonneg.2 hpm1) (sub_nonneg.2 hL)]
  have hpow : s ^ m = S ^ m * τ ^ m := by rw [← mul_pow, ← hsτ]
  have h5 : s ^ m * (-Real.log s) = S ^ m * (τ ^ m * (-Real.log S) + τ ^ m * (-Real.log τ)) := by
    rw [hpow, hlog]; ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left h4 hSm.le

theorem log_two_le' : Real.log 2 ≤ 7 / 10 := by
  have := Real.log_two_lt_d9; norm_num at this; linarith

/-- `|log S| ≤ (7/10) e` from the checked exponent `1 ≤ S 2^e`, `S ≤ 1`. -/
theorem abs_log_le_of_pow {S : ℝ} {e : ℕ} (hS0 : 0 < S) (hS1 : S ≤ 1) (he : (1 : ℝ) ≤ S * 2 ^ e) :
    |Real.log S| ≤ (e : ℝ) * (7 / 10) := by
  have hl : Real.log S ≤ 0 := Real.log_nonpos hS0.le hS1
  rw [abs_of_nonpos hl]
  have : Real.log ((2 : ℝ) ^ e)⁻¹ ≤ Real.log S := by
    apply Real.log_le_log (by positivity)
    rw [← one_div, div_le_iff₀ (by positivity)]; exact he
  rw [Real.log_inv, Real.log_pow] at this
  nlinarith [log_two_le', Nat.cast_nonneg (α := ℝ) e, Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end CatalanCore.Uniform.Decay.Breakpoint
