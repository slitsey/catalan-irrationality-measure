import CatalanLambda.Decay.ThmNRiemann

/-!
# Theorem N_ρ: the closed form of `U^τ` off the real axis

For `Re z < 0`:
`U^τ(z) = 1 - x log|z| - (1-x) log|1-z| - y arctan (y / (x² + y² - x))`
(this is the soundness lemma `Utau_closed_form` of BT §5.2).
-/

open Finset MeasureTheory intervalIntegral

namespace CatalanLambda.Decay

lemma Utau_integrand (z : ℂ) (t : ℝ) :
    -Real.log ‖z - (t : ℂ)‖ = -(1 / 2 * Real.log ((t - z.re) ^ 2 + z.im ^ 2)) := by
  have hn : 0 ≤ ‖z - (t : ℂ)‖ := norm_nonneg _
  have h2 := norm_sub_real_sq z t
  by_cases h0 : ‖z - (t : ℂ)‖ = 0
  · rw [h0] at h2
    have : (t - z.re) ^ 2 + z.im ^ 2 = 0 := by nlinarith
    rw [h0, this]; simp
  · have hp : 0 < ‖z - (t : ℂ)‖ := lt_of_le_of_ne hn (Ne.symm h0)
    have : (t - z.re) ^ 2 + z.im ^ 2 = ‖z - (t : ℂ)‖ ^ 2 := by rw [h2]; ring
    rw [this, Real.log_pow]; push_cast; ring

/-- Antiderivative of `½ log((t-x)² + y²)`. -/
noncomputable def Gprim (x y t : ℝ) : ℝ :=
  (t - x) * (1 / 2 * Real.log ((t - x) ^ 2 + y ^ 2)) - (t - x) + y * Real.arctan ((t - x) / y)

lemma hasDerivAt_Gprim (x y t : ℝ) (hy : y ≠ 0) :
    HasDerivAt (Gprim x y) (1 / 2 * Real.log ((t - x) ^ 2 + y ^ 2)) t := by
  have hq : 0 < (t - x) ^ 2 + y ^ 2 := by positivity
  have hu : HasDerivAt (fun s : ℝ => s - x) 1 t := (hasDerivAt_id t).sub_const x
  have hq' : HasDerivAt (fun s : ℝ => (s - x) ^ 2 + y ^ 2) (2 * (t - x)) t := by
    have := (hu.pow 2).add_const (y ^ 2)
    simpa using this
  have hlog := hq'.log hq.ne'
  have hp := hu.mul (hlog.const_mul (1 / 2))
  have hg : HasDerivAt (fun s : ℝ => (s - x) / y) (1 / y) t := hu.div_const y
  have hat := hg.arctan
  have hall := (hp.sub hu).add (hat.const_mul y)
  convert hall using 1
  · funext s; simp [Gprim]
  · field_simp
    ring

lemma Utau_key (x y : ℝ) (hx : x < 0) :
    ∫ t in (0 : ℝ)..1, -(1 / 2 * Real.log ((t - x) ^ 2 + y ^ 2))
      = 1 - x * (Real.log (x ^ 2 + y ^ 2) / 2) - (1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)
        - y * Real.arctan (y / (x ^ 2 + y ^ 2 - x)) := by
  by_cases hy0 : y = 0
  · subst hy0
    simp only [zero_pow two_ne_zero, add_zero, zero_mul, sub_zero]
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (s - x) * Real.log (s - x) - (s - x)) (Real.log (t - x)) t := by
      intro t ht
      have ht' : 0 ≤ t := by rw [Set.uIcc_of_le zero_le_one] at ht; exact ht.1
      have hpos : t - x ≠ 0 := by linarith
      have hu : HasDerivAt (fun s : ℝ => s - x) 1 t := (hasDerivAt_id t).sub_const x
      have := (hu.mul (hu.log hpos)).sub hu
      convert this using 1
      field_simp; ring
    have hc : ∀ t ∈ Set.uIcc (0 : ℝ) 1, -(1 / 2 * Real.log ((t - x) ^ 2)) = -Real.log (t - x) := by
      intro t ht
      have ht' : 0 ≤ t := by rw [Set.uIcc_of_le zero_le_one] at ht; exact ht.1
      have hpos : 0 < t - x := by linarith
      rw [Real.log_pow]; push_cast; ring
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hder]
    · have hx2 : Real.log (x ^ 2) = 2 * Real.log (-x) := by
        rw [show x ^ 2 = (-x) ^ 2 by ring, Real.log_pow]; push_cast; ring
      have h1x : Real.log ((1 - x) ^ 2) = 2 * Real.log (1 - x) := by
        rw [Real.log_pow]; push_cast; ring
      rw [hx2, h1x]
      simp only [sub_zero, zero_sub, sub_neg_eq_add, zero_add, mul_zero, Real.arctan_zero]
      ring_nf
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have ht' : 0 ≤ t := by rw [Set.uIcc_of_le zero_le_one] at ht; exact ht.1
      have hpos : t - x ≠ 0 := by linarith
      exact (ContinuousAt.log (f := fun s : ℝ => s - x) (by fun_prop) hpos).continuousWithinAt
  · rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_Gprim x y t hy0)]
    · simp only [Gprim]
      have hy2 : y ^ 2 ≠ 0 := by positivity
      have hxx : x * (1 - x) < 0 := by nlinarith
      have hab : (1 - x) / y * (x / y) = x * (1 - x) / y ^ 2 := by field_simp
      have hsum : Real.arctan ((1 - x) / y) + Real.arctan (x / y)
          = Real.arctan (y / (x ^ 2 + y ^ 2 - x)) := by
        have hlt : x * (1 - x) / y ^ 2 < 0 := div_neg_of_neg_of_pos hxx (by positivity)
        rw [Real.arctan_add (by rw [hab]; linarith)]
        congr 1
        have hd : x ^ 2 + y ^ 2 - x ≠ 0 := by nlinarith [sq_pos_of_ne_zero hy0]
        have e1 : (1 - x) / y + x / y = 1 / y := by field_simp; ring
        have e2 : 1 - (1 - x) / y * (x / y) = (x ^ 2 + y ^ 2 - x) / y ^ 2 := by
          rw [hab]; field_simp; ring
        rw [e1, e2, div_div_eq_mul_div]
        field_simp
      have hneg : Real.arctan ((0 - x) / y) = -Real.arctan (x / y) := by
        rw [zero_sub, neg_div, Real.arctan_neg]
      have l0 : Real.log ((0 - x) ^ 2 + y ^ 2) = Real.log (x ^ 2 + y ^ 2) := by ring_nf
      rw [hneg, l0, ← hsum]
      ring
    · apply ContinuousOn.intervalIntegrable
      intro t _
      have hq : (t - x) ^ 2 + y ^ 2 ≠ 0 := by positivity
      have : ContinuousAt (fun s : ℝ => 1 / 2 * Real.log ((s - x) ^ 2 + y ^ 2)) t :=
        continuousAt_const.mul (ContinuousAt.log (by fun_prop) hq)
      exact this.continuousWithinAt

/-- **Closed form of `U^τ`** for `Re z < 0`. -/
theorem Utau_closed_form {z : ℂ} (hz : z.re < 0) :
    Utau z = 1 - z.re * (Real.log (z.re ^ 2 + z.im ^ 2) / 2)
      - (1 - z.re) * (Real.log ((1 - z.re) ^ 2 + z.im ^ 2) / 2)
      - z.im * Real.arctan (z.im / (z.re ^ 2 + z.im ^ 2 - z.re)) := by
  unfold Utau
  simp_rw [Utau_integrand z]
  exact Utau_key z.re z.im hz

end CatalanLambda.Decay
