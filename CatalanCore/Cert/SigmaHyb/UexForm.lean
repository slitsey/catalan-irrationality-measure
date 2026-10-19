module

public import CatalanCore.Cert.SigmaHyb.UBox
public import CatalanCore.Decay.Rect.Decompose
public import CatalanLambda.Cert.Bridge
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Closed form of the extra-node potential `U^ex` at `L = 1/4` in terms of `U^τ`

`Uex L s = (L/2) (Utau ((s-1)/L) - log L)` for `Re s < 1` (substitution `u = 1 + L t`), hence
`Unu (1/8) ⟨x, y⟩ = Utau x y + (1/8) Utau (4x-4) (4y) + (1/4) log 2` (legacy closed forms).
-/

open Real MeasureTheory intervalIntegral

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Decay CatalanCore.Decay

set_option maxRecDepth 100000

theorem Uex_scale {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : s.re < 1) :
    CatalanCore.Decay.Uex L s = (L / 2) * (CatalanLambda.Decay.Utau ((s - 1) / (L : ℂ)) - Real.log L) := by
  unfold CatalanCore.Decay.Uex
  have hne : ∀ t : ℝ, 0 ≤ t → ‖(s - 1) / (L : ℂ) - (t : ℂ)‖ ≠ 0 := by
    intro t ht h
    have h0 : (s - 1) / (L : ℂ) - (t : ℂ) = 0 := norm_eq_zero.mp h
    have := congrArg Complex.re h0
    simp [Complex.div_ofReal_re] at this
    have h2 : s.re - 1 < 0 := by linarith
    have h3 : (s.re - 1) / L < 0 := div_neg_of_neg_of_pos h2 hL
    linarith [this]
  have hsub : ∀ t : ℝ, 0 ≤ t → elog s ((L * t + 1 : ℝ) : ℂ)
      = -Real.log L + (-Real.log ‖(s - 1) / (L : ℂ) - (t : ℂ)‖) := by
    intro t ht
    have e : s - ((L * t + 1 : ℝ) : ℂ) = (L : ℂ) * ((s - 1) / (L : ℂ) - (t : ℂ)) := by
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast; field_simp; ring
    unfold elog
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
      Real.log_mul hL.ne' (hne t ht)]
    ring
  have hcomp := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1)
    (fun u : ℝ => elog s (u : ℂ)) hL.ne' 1
  have hint : (∫ t in (0 : ℝ)..1, elog s ((L * t + 1 : ℝ) : ℂ)) =
      -Real.log L + CatalanLambda.Decay.Utau ((s - 1) / (L : ℂ)) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => -Real.log L + (-Real.log ‖(s - 1) / (L : ℂ) - (t : ℂ)‖))
      (fun t ht => hsub t (by rw [Set.uIcc_of_le zero_le_one] at ht; exact ht.1))]
    unfold CatalanLambda.Decay.Utau
    have hc : ContinuousOn (fun t : ℝ => -Real.log ‖(s - 1) / (L : ℂ) - (t : ℂ)‖) (Set.uIcc 0 1) := by
      apply ContinuousOn.neg
      apply ContinuousOn.log
      · fun_prop
      · intro t ht; exact hne t (by rw [Set.uIcc_of_le zero_le_one] at ht; exact ht.1)
    rw [intervalIntegral.integral_add intervalIntegrable_const hc.intervalIntegrable]
    simp
  simp only [mul_zero, zero_add, mul_one] at hcomp
  have h2 : (∫ u in (1 : ℝ)..L + 1, elog s (u : ℂ)) = L * (-Real.log L + CatalanLambda.Decay.Utau ((s - 1) / (L : ℂ))) := by
    rw [← hint, hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
  rw [add_comm 1 L, h2]
  ring

theorem Uex_quarter (α : ℝ) (hα : α = 1 / 8) {s : ℂ} (hs : s.re < 1) :
    CatalanCore.Decay.Uex (2 * α) s
      = (1 / 8) * CatalanLambda.Decay.Utau (4 * (s - 1)) + (1 / 4) * Real.log 2 := by
  have hL : 2 * α = 1 / 4 := by rw [hα]; norm_num
  rw [hL, Uex_scale (by norm_num) hs]
  have e : (s - 1) / (((1 / 4 : ℝ)) : ℂ) = 4 * (s - 1) := by
    push_cast; field_simp
  rw [e]
  have l4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv]
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  rw [l4]; ring

/-- `s = 1`: `Uex L 1 = (L/2)(1 - log L)`. -/
theorem Uex_one {L : ℝ} (hL : 0 < L) :
    CatalanCore.Decay.Uex L 1 = (L / 2) * (1 - Real.log L) := by
  unfold CatalanCore.Decay.Uex
  have h1 : ∀ u ∈ Set.uIcc (1 : ℝ) (1 + L), elog (1 : ℂ) (u : ℂ) = -Real.log (u - 1) := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    unfold elog
    have : (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, Real.log_abs, ← Real.log_neg_eq_log]
    ring_nf
  rw [intervalIntegral.integral_congr h1]
  have := intervalIntegral.integral_comp_sub_right (a := 1) (b := 1 + L) (fun v : ℝ => -Real.log v) 1
  simp only [sub_self, add_sub_cancel_left] at this
  rw [this, intervalIntegral.integral_neg, integral_log]
  simp
  ring

end CatalanCore.Cert.SigmaHyb
