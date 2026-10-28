module

public import CatalanCore.Uniform.Decay.Tools.PotentialReal
public import CatalanCore.Decay.Rect.Energy2

@[expose] public section

/-!
# Continuity of the node potential `Unu` on the real axis (lane D, package D2)

`x ↦ Unu α x` is continuous on `x ≤ 0` (indeed `Utau` is continuous on all of `ℝ`).  Used by the
Darboux cap bridge, which needs continuity of the atomic `g` on `[-r0, 0]`.  Closed forms come from
`Tools.PotentialReal.integral_pow_mul_log_real`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open CatalanCore.Uniform.Decay.Tools CatalanLambda.Decay CatalanCore.Decay

theorem Hk0_eq (r t : ℝ) : Hk 0 r t = (t - r) * Real.log (t - r) - t := by
  simp [Hk]

theorem continuous_Hk0_r (t : ℝ) : Continuous (fun r : ℝ => Hk 0 r t) := by
  have : (fun r : ℝ => Hk 0 r t) = fun r => (t - r) * Real.log (t - r) - t := by
    funext r; exact Hk0_eq r t
  rw [this]
  exact (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).sub continuous_const

theorem Utau_real (x : ℝ) : Utau (x : ℂ) = -(Hk 0 x 1 - Hk 0 x 0) := by
  have h := integral_pow_mul_log_real 0 x
  simp only [pow_zero, one_mul] at h
  unfold Utau
  have e : ∀ t : ℝ, -Real.log ‖(x : ℂ) - (t : ℂ)‖ = -Real.log (t - x) := by
    intro t
    have : ‖(x : ℂ) - (t : ℂ)‖ = |t - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [this, Real.log_abs]
  simp_rw [e]
  rw [intervalIntegral.integral_neg, h]

theorem Uex_real {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ≤ 0) :
    Uex L (x : ℂ) = -(1 / 2) * (Hk 0 x (1 + L) - Hk 0 x 1) := by
  have h := integral_pow_mul_log_real_of_le 0 x 1 (1 + L) (by linarith)
    (fun hmem => by linarith [hmem.1])
  simp only [pow_zero, one_mul] at h
  unfold Uex
  have e : ∀ u : ℝ, elog (x : ℂ) (u : ℂ) = -Real.log (u - x) := by
    intro u
    unfold elog
    have : ‖(x : ℂ) - (u : ℂ)‖ = |u - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [this, Real.log_abs]
  simp_rw [e]
  rw [intervalIntegral.integral_neg, h]
  ring

theorem continuous_Utau_real : Continuous (fun x : ℝ => Utau (x : ℂ)) := by
  have : (fun x : ℝ => Utau (x : ℂ)) = fun x => -(Hk 0 x 1 - Hk 0 x 0) := by
    funext x; exact Utau_real x
  rw [this]
  exact ((continuous_Hk0_r 1).sub (continuous_Hk0_r 0)).neg

/-- `Unu` is continuous along the real axis on `x ≤ 0`. -/
theorem continuousOn_Unu_real {α : ℝ} (hα : 0 ≤ α) :
    ContinuousOn (fun x : ℝ => Unu α (x : ℂ)) (Set.Iic 0) := by
  have hex : ContinuousOn (fun x : ℝ => Uex (2 * α) (x : ℂ)) (Set.Iic 0) := by
    have hc : Continuous (fun x : ℝ => -(1 / 2) * (Hk 0 x (1 + 2 * α) - Hk 0 x 1)) :=
      continuous_const.mul ((continuous_Hk0_r _).sub (continuous_Hk0_r _))
    refine hc.continuousOn.congr (fun x hx => ?_)
    exact Uex_real (by linarith) hx
  unfold Unu
  exact continuous_Utau_real.continuousOn.add hex

end CatalanCore.Uniform.Decay.Spline
