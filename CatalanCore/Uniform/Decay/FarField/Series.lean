import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
set_option Elab.async false

/-!
# Truncated logarithm series (lane D, package D15)

For `‖q‖ ≤ ρ < 1`:  `log ‖1 - q‖ = - Re ∑_{k=1}^K q^k / k + (error)`, `|error| ≤ ρ^(K+1) / ((K+1)(1-ρ))`.
This is the scalar estimate behind the far-field (multipole) expansion of a log potential.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset

/-- The `K`-term partial sum `∑_{k=1}^K q^k / k`. -/
noncomputable def logPart (q : ℂ) (K : ℕ) : ℂ :=
  ∑ k ∈ range K, q ^ (k + 1) / ((k + 1 : ℕ) : ℂ)

theorem logPart_succ (q : ℂ) (K : ℕ) :
    logPart q (K + 1) = logPart q K + q ^ (K + 1) / ((K + 1 : ℕ) : ℂ) := by
  unfold logPart; rw [Finset.sum_range_succ]

/-- **Tail bound of the logarithm series.** -/
theorem log_series_tail {q : ℂ} {ρ : ℝ} (hq : ‖q‖ ≤ ρ) (hρ : ρ < 1) (K : ℕ) :
    |Real.log ‖1 - q‖ + (logPart q K).re| ≤ ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg q).trans hq
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq hρ
  have hS := Complex.hasSum_taylorSeries_neg_log hq1
  have hsplit := Summable.sum_add_tsum_nat_add (K + 1) hS.summable
  rw [hS.tsum_eq] at hsplit
  set T : ℂ := ∑' n : ℕ, q ^ (n + (K + 1)) / ((n + (K + 1) : ℕ) : ℂ) with hT
  have hfirst : ∑ n ∈ range (K + 1), q ^ n / (n : ℂ) = logPart q K := by
    unfold logPart
    rw [Finset.sum_range_succ']
    simp
  rw [hfirst] at hsplit
  have hlog : Real.log ‖1 - q‖ = (-(logPart q K + T)).re := by
    rw [hsplit, ← Complex.log_re]
    simp
  have hre : Real.log ‖1 - q‖ + (logPart q K).re = -T.re := by
    rw [hlog]; simp
  rw [hre, abs_neg]
  refine (Complex.abs_re_le_norm T).trans ?_
  have hg : HasSum (fun n : ℕ => ρ ^ (K + 1) / (K + 1) * ρ ^ n)
      (ρ ^ (K + 1) / (K + 1) * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ).mul_left _
  have := tsum_of_norm_bounded hg (f := fun n : ℕ => q ^ (n + (K + 1)) / ((n + (K + 1) : ℕ) : ℂ)) (by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have hn : (K + 1 : ℝ) ≤ ((n + (K + 1) : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpos : (0 : ℝ) < K + 1 := by positivity
    calc ‖q‖ ^ (n + (K + 1)) / ((n + (K + 1) : ℕ) : ℝ)
        ≤ ρ ^ (n + (K + 1)) / ((n + (K + 1) : ℕ) : ℝ) := by
          gcongr
      _ ≤ ρ ^ (n + (K + 1)) / (K + 1) := by
          apply div_le_div_of_nonneg_left (by positivity) hpos hn
      _ = ρ ^ (K + 1) / (K + 1) * ρ ^ n := by ring)
  have h1ρ : 0 < 1 - ρ := by linarith
  calc ‖T‖ ≤ ρ ^ (K + 1) / (K + 1) * (1 - ρ)⁻¹ := this
    _ = ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) := by field_simp

end CatalanCore.Uniform.Decay.FarField
