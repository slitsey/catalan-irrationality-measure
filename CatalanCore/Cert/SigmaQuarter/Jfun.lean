module

public import CatalanCore.Cert.SigmaHyb.JfunH

@[expose] public section
open Real MeasureTheory intervalIntegral
namespace CatalanCore.Cert.SigmaQuarter
open CatalanLambda.Decay CatalanCore.Decay CatalanCore.Cert.SigmaHyb
set_option maxRecDepth 100000

theorem Gan_cont_quarter : ContinuousOn Gan (Set.Icc 1 (3 / 2)) := by
  have hl : ContinuousOn Real.log (Set.Icc (1 : ℝ) (3 / 2)) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; intro h; have := hx.1; linarith [h])
  have hA : ContinuousOn (fun u : ℝ => u ^ 2 / 2 * Real.log u) (Set.Icc (1 : ℝ) (3 / 2)) :=
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

theorem Iu_quarter : Iu (1 / 4) = 3 / 4 - (9 / 8) * Real.log (3 / 2) - (1 / 8) * Real.log 2 := by
  unfold Iu
  have e : (1 : ℝ) + 2 * (1 / 4) = 3 / 2 := by norm_num
  rw [e]
  have h1 : ∀ u ∈ Set.uIcc (1 : ℝ) (3 / 2), Utau (u : ℂ) = 1 + (u - 1) * Real.log (u - 1) - u * Real.log u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    exact Utau_ge1 hu.1
  rw [intervalIntegral.integral_congr h1]
  have hc : Continuous fun u : ℝ => 1 + (u - 1) * Real.log (u - 1) - u * Real.log u :=
    (continuous_const.add (Real.continuous_mul_log.comp (continuous_id.sub continuous_const))).sub Real.continuous_mul_log
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num) Gan_cont_quarter
    (fun x hx => (Gan_deriv hx.1).hasDerivWithinAt) (hc.intervalIntegrable _ _)]
  unfold Gan
  have l2 : Real.log (3 / 2 - 1 : ℝ) = -Real.log 2 := by
    have : (3 / 2 - 1 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [this, Real.log_inv]
  simp only [sub_self, Real.log_one, Real.log_zero]
  rw [l2]
  norm_num
  ring

theorem Jfun_quarter : Jfun (1 / 4) = 75 / 32 - (9 / 8) * Real.log (3 / 2) - (1 / 16) * Real.log 2 := by
  unfold Jfun gJ
  rw [Iu_quarter]
  have l2 : Real.log (2 * (1 / 4) : ℝ) = -Real.log 2 := by
    have : (2 * (1 / 4) : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [this, Real.log_inv]
  rw [l2]
  ring

theorem logThreeHalf_le : Real.log (3 / 2) ≤ 4054651082 / 10 ^ 10 := by
  have h := (CatalanLambda.Cert.log_atanh_bounds (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 12).2
  have e : Real.log (1 + 1 / 5) - Real.log (1 - 1 / 5) = Real.log (3 / 2) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e] at h
  refine h.trans ?_
  simp only [CatalanLambda.Cert.atS, CatalanLambda.Cert.atT]
  norm_num

theorem Inu_le : (184428 / 100000 : ℝ) ≤ CatalanCore.Decay.Jfun (1 / 4) := by
  rw [Jfun_quarter]
  have h1 := Real.log_two_lt_d9
  have h2 := logThreeHalf_le
  norm_num at h1 ⊢
  linarith

end CatalanCore.Cert.SigmaQuarter
