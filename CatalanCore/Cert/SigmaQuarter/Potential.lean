module

public import CatalanCore.Decay.Rect.Energy2
public import CatalanLambda.Decay.ThmNPoint
public import CatalanLambda.Decay.ThmNUtauForm

@[expose] public section

/-! Affine interval-potential identities, shared by every border ratio. -/

open MeasureTheory intervalIntegral

namespace CatalanCore.Cert.SigmaQuarter

open CatalanLambda.Decay CatalanCore.Decay

lemma elog_real_integrable (x a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => elog (x : ℂ) (u : ℂ)) volume a b := by
  have h := ((intervalIntegral.intervalIntegrable_log' (a := a - x) (b := b - x)).comp_sub_right x).neg
  simp only [sub_add_cancel] at h
  have e : (fun u : ℝ => elog (x : ℂ) (u : ℂ)) = fun u => -Real.log (u - x) := by
    funext u
    unfold elog
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    rw [← Real.log_neg_eq_log (u - x)]
    congr 2
    ring
  rw [e]
  exact h

lemma elog_integrable (s : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => elog s (u : ℂ)) volume a b := by
  by_cases hi : s.im = 0
  · have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [hi])
    rw [hs]
    exact elog_real_integrable _ _ _
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply Real.continuousOn_log.comp (by fun_prop : ContinuousOn (fun u : ℝ => ‖s - (u : ℂ)‖) (Set.uIcc a b))
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz
    have hz' := sub_eq_zero.mp (norm_eq_zero.mp hz)
    have := congrArg Complex.im hz'
    simp at this
    exact hi this

lemma elog_scale_ae (s : ℂ) {A : ℝ} (hA : 0 < A) :
    (fun t : ℝ => elog s ((A * t : ℝ) : ℂ)) =ᵐ[volume]
      fun t => elog (s / (A : ℂ)) (t : ℂ) - Real.log A := by
  filter_upwards [volume.ae_ne (s.re / A)] with t ht
  have hn : s / (A : ℂ) ≠ (t : ℂ) := by
    intro he
    have := congrArg Complex.re he
    simp [Complex.div_ofReal_re] at this
    exact ht this.symm
  have h := CatalanLambda.Decay.elog_scale hA (s / (A : ℂ)) (t : ℂ)
  have hAC : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  simpa only [mul_div_cancel₀ _ hAC, ← Complex.ofReal_mul, if_neg hn] using h

lemma interval_potential_scale (s : ℂ) {A : ℝ} (hA : 0 < A) :
    (∫ u in (0 : ℝ)..A, elog s (u : ℂ)) =
      A * Utau (s / (A : ℂ)) - A * Real.log A := by
  have he := intervalIntegral.integral_congr_ae (a := (0 : ℝ)) (b := 1)
    ((elog_scale_ae s hA).mono (fun _ h _ => h))
  rw [intervalIntegral.integral_sub (elog_integrable _ _ _)
    (intervalIntegrable_const), intervalIntegral.integral_const] at he
  have hc := intervalIntegral.integral_comp_mul_left
    (fun u : ℝ => elog s (u : ℂ)) hA.ne' (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul, sub_zero] at hc he
  unfold Utau
  unfold elog at he hc
  rw [hc] at he
  have hh := congrArg (fun x : ℝ => A * x) he
  simp only [mul_sub, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at hh
  exact hh

theorem Unu_interval (s : ℂ) {α : ℝ} (hα : 0 ≤ α) :
    Unu α s = (1 / 2) * Utau s +
      ((1 + 2 * α) / 2) * Utau (s / ((1 + 2 * α : ℝ) : ℂ)) -
      ((1 + 2 * α) / 2) * Real.log (1 + 2 * α) := by
  have hs := interval_potential_scale s (A := 1 + 2 * α) (by positivity)
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (elog_integrable s 0 1) (elog_integrable s 1 (1 + 2 * α))
  unfold Unu Uex Utau
  unfold elog at hs ha ⊢
  unfold Utau at hs
  linarith

theorem Unu_quarter (s : ℂ) :
    Unu (1 / 4) s = (1 / 2) * Utau s + (3 / 4) * Utau (s / (3 / 2 : ℂ)) -
      (3 / 4) * Real.log (3 / 2) := by
  have h := Unu_interval s (α := 1 / 4) (by norm_num)
  norm_num at h ⊢
  exact h

end CatalanCore.Cert.SigmaQuarter
