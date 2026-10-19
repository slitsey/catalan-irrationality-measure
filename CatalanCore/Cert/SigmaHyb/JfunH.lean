module

public import CatalanCore.Decay.Rect.Asymp
public import CatalanLambda.Cert.LogBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# `Jfun (1/8) = 243/128 - (1/32) log 2 - (25/32) log (5/4)` and a rational lower bound

`U^τ(u) = 1 + (u-1) log (u-1) - u log u` for real `u ≥ 1`, and the antiderivative
`G u = u - (u²/2) log u + u²/4 + ((u-1)²/2) log (u-1) - (u-1)²/4`.
-/

open Real MeasureTheory intervalIntegral

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Decay CatalanCore.Decay

set_option maxRecDepth 100000

theorem Utau_ge1 {u : ℝ} (hu : 1 ≤ u) :
    Utau (u : ℂ) = 1 + (u - 1) * Real.log (u - 1) - u * Real.log u := by
  unfold Utau
  have h1 : ∀ t : ℝ, -Real.log ‖(u : ℂ) - (t : ℂ)‖ = (fun v : ℝ => -Real.log v) (u - t) := by
    intro t
    simp only
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_left (fun v : ℝ => -Real.log v) u]
  rw [intervalIntegral.integral_neg, integral_log]
  simp only [sub_zero]
  ring

noncomputable def Gan (u : ℝ) : ℝ :=
  u - u ^ 2 / 2 * Real.log u + u ^ 2 / 4 + (u - 1) ^ 2 / 2 * Real.log (u - 1) - (u - 1) ^ 2 / 4

theorem Gan_deriv {u : ℝ} (hu : 1 < u) :
    HasDerivAt Gan (1 + (u - 1) * Real.log (u - 1) - u * Real.log u) u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2 / 2 * Real.log u) (u * Real.log u + u / 2) u :=
    (((hasDerivAt_pow 2 u).div_const 2).mul (Real.hasDerivAt_log hu0.ne')).congr_deriv
      (by field_simp; ring)
  have hs : HasDerivAt (fun u : ℝ => u - 1) 1 u := (hasDerivAt_id u).sub_const 1
  have h2 : HasDerivAt (fun u : ℝ => (u - 1) ^ 2 / 2 * Real.log (u - 1))
      ((u - 1) * Real.log (u - 1) + (u - 1) / 2) u :=
    (((hs.pow 2).div_const 2).mul (hs.log hu1.ne')).congr_deriv (by first | (simp only [Pi.pow_apply]; field_simp; ring) | (field_simp; ring))
  have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 4) (u / 2) u :=
    ((hasDerivAt_pow 2 u).div_const 4).congr_deriv (by ring)
  have h4 : HasDerivAt (fun u : ℝ => (u - 1) ^ 2 / 4) ((u - 1) / 2) u :=
    ((hs.pow 2).div_const 4).congr_deriv (by first | (simp only [Pi.pow_apply]; ring) | ring)
  exact (((((hasDerivAt_id u).sub h1).add h3).add h2).sub h4).congr_deriv (by ring)

theorem Gan_cont : ContinuousOn Gan (Set.Icc 1 (5 / 4)) := by
  have hl : ContinuousOn Real.log (Set.Icc (1 : ℝ) (5 / 4)) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; intro h; have := hx.1; linarith [h])
  have hA : ContinuousOn (fun u : ℝ => u ^ 2 / 2 * Real.log u) (Set.Icc (1 : ℝ) (5 / 4)) :=
    ContinuousOn.mul (by fun_prop) hl
  have hm : Continuous fun x : ℝ => (x - 1) * Real.log (x - 1) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have h2 : Continuous fun x : ℝ => (x - 1) ^ 2 / 2 * Real.log (x - 1) := by
    have : (fun x : ℝ => (x - 1) ^ 2 / 2 * Real.log (x - 1)) = fun x => (x - 1) / 2 * ((x - 1) * Real.log (x - 1)) := by
      funext x; ring
    rw [this]; exact ((continuous_id.sub continuous_const).div_const 2).mul hm
  have h3 : Continuous fun u : ℝ => u ^ 2 / 4 := by fun_prop
  have h4 : Continuous fun u : ℝ => (u - 1) ^ 2 / 4 := by fun_prop
  unfold Gan
  exact (((continuousOn_id.sub hA).add h3.continuousOn).add h2.continuousOn).sub h4.continuousOn

theorem Iu_eighth : Iu (1 / 8) = 3 / 8 - (25 / 32) * Real.log (5 / 4) - (1 / 16) * Real.log 2 := by
  unfold Iu
  have e : (1 : ℝ) + 2 * (1 / 8) = 5 / 4 := by norm_num
  rw [e]
  have h1 : ∀ u ∈ Set.uIcc (1 : ℝ) (5 / 4), Utau (u : ℂ) = 1 + (u - 1) * Real.log (u - 1) - u * Real.log u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact Utau_ge1 hu.1
  rw [intervalIntegral.integral_congr h1]
  have hc : Continuous fun u : ℝ => 1 + (u - 1) * Real.log (u - 1) - u * Real.log u :=
    (continuous_const.add (Real.continuous_mul_log.comp (continuous_id.sub continuous_const))).sub Real.continuous_mul_log
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num) Gan_cont
    (fun x hx => (Gan_deriv hx.1).hasDerivWithinAt) (hc.intervalIntegrable _ _)]
  unfold Gan
  have l4 : Real.log (5 / 4 - 1 : ℝ) = -(2 * Real.log 2) := by
    have : (5 / 4 - 1 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) := by norm_num
    rw [this, Real.log_zpow]; push_cast; ring
  simp only [sub_self, Real.log_one, Real.log_zero]
  rw [l4]
  norm_num
  ring

theorem Jfun_eighth : Jfun (1 / 8) = 243 / 128 - (1 / 32) * Real.log 2 - (25 / 32) * Real.log (5 / 4) := by
  unfold Jfun gJ
  rw [Iu_eighth]
  have l4 : Real.log (2 * (1 / 8) : ℝ) = -(2 * Real.log 2) := by
    have : (2 * (1 / 8) : ℝ) = (2 : ℝ) ^ (-2 : ℤ) := by norm_num
    rw [this, Real.log_zpow]; push_cast; ring
  rw [l4]
  ring

section
open CatalanLambda.Cert

theorem log54_le : Real.log (5 / 4) ≤ 2231435514 / 10 ^ 10 := by
  have h := (log_atanh_bounds (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 8).2
  have e : Real.log (1 + 1 / 9) - Real.log (1 - 1 / 9) = Real.log (5 / 4) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e] at h
  refine h.trans ?_
  simp only [atS, atT]
  norm_num

theorem Inu_le : ((17024457 / 10 ^ 7 : ℚ) : ℝ) ≤ CatalanCore.Decay.Jfun (((1 / 8 : ℚ)) : ℝ) := by
  have e : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by push_cast; norm_num
  rw [e, Jfun_eighth]
  have h1 := Real.log_two_lt_d9
  have h2 := log54_le
  push_cast
  norm_num at h1 ⊢
  linarith

end

end CatalanCore.Cert.SigmaHyb
