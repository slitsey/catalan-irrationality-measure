module

public import CatalanCore.Cert.SigmaQuarter.Potential
public import CatalanCore.Decay.Rect.CertG
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaQuarter

open CatalanLambda.Decay CatalanCore.Decay

theorem interval_potential_upper (s : ℂ) (a b : ℝ) (hab : a ≤ b) (hi : 0 < |s.im|) :
    (∫ t in a..b, elog s (t : ℂ)) ≤ (b - a) * (-Real.log |s.im|) := by
  have hp : ∀ t : ℝ, |s.im| ≤ ‖s - (t : ℂ)‖ := by
    intro t
    simpa using Complex.abs_im_le_norm (s - (t : ℂ))
  have hm := intervalIntegral.integral_mono_on hab (elog_integrable s a b)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Real.log |s.im|) volume a b)
    (fun t _ => by
      unfold elog
      linarith [Real.log_le_log hi (hp t)])
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm

theorem Unu_upper (s : ℂ) {α : ℝ} (hα : 0 ≤ α) (hi : 0 < |s.im|) :
    Unu α s ≤ -(1 + α) * Real.log |s.im| := by
  have h1 := interval_potential_upper s 0 1 zero_le_one hi
  have h2 := interval_potential_upper s 1 (1 + 2 * α) (by linarith) hi
  unfold Unu Uex Utau
  unfold elog at h1 h2
  unfold elog
  nlinarith

theorem tail_core (sl r0 epsilon : ℝ)
    (hsl0 : 2 ≤ sl) (hsl1 : sl ≤ 3) (hr0 : 0 ≤ r0) (hr1 : r0 ≤ 1 / 5)
    (he : epsilon ≤ 1 / 1000) {K : ℕ} (c : Fin K → ℂ) (m : Fin K → ℝ)
    (hm : ∀ k, 0 ≤ m k) (hsum : ∑ k, m k = 1) (hn : ∀ k, ‖c k‖ ≤ 16)
    (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (3 : ℝ) ≤
      gAlpha (1 / 2048) epsilon c m (1 / 4) (Unu (1 / 4))
        ⟨-r0 + δ - u, sl * u⟩ := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-r0 + δ - u, sl * u⟩ with hz
  have hd := abs_le.mp (hδ.trans (by norm_num : (1 / 2 ^ 30 : ℝ) ≤ 1 / 100))
  have hr : z.re ^ 2 ≤ (u + 1 / 4) ^ 2 := by
    apply sq_le_sq'
    · dsimp [z]; linarith
    · dsimp [z]; linarith
  have hzs : ‖z‖ ^ 2 ≤ 16 * u ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him : z.im = sl * u := rfl
    rw [him]
    have hy : (sl * u) ^ 2 ≤ (3 * u) ^ 2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr (by nlinarith)
    nlinarith
  have hzn : ‖z‖ ≤ 4 * u := by nlinarith [norm_nonneg z]
  have hp : ∀ k, ‖z - c k‖ ^ 2 + (1 / 2048 : ℝ) ^ 2 ≤ 256 * u ^ 2 := by
    intro k
    have hn' := norm_sub_le z (c k)
    have hd' : ‖z - c k‖ ≤ 15 * u := by linarith [hn k]
    have hsq : ‖z - c k‖ ^ 2 ≤ (15 * u) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hd'
    nlinarith
  have hUs : -(1 / 2) * Real.log (256 * u ^ 2) ≤
      CatalanLambda.Decay.Usig (1 / 2048 : ℝ) c m z := by
    have h1 : ∀ k, m k * (-(1 / 2) * Real.log (256 * u ^ 2)) ≤
        m k * krho (1 / 2048 : ℝ) z (c k) := by
      intro k
      unfold krho
      apply mul_le_mul_of_nonneg_left _ (hm k)
      have hl := Real.log_le_log (by positivity : 0 < ‖z - c k‖ ^ 2 + (1 / 2048 : ℝ) ^ 2) (hp k)
      linarith
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h1 k)
    rw [← Finset.sum_mul, hsum, one_mul] at hh
    exact hh
  have hIm : |z.im| = sl * u := abs_of_pos (by change 0 < sl * u; nlinarith)
  have hUn := Unu_upper z (α := 1 / 4) (by norm_num) (by rw [hIm]; positivity)
  rw [hIm] at hUn
  have hlog : -(4 : ℝ) ≤ Real.log (sl * u) - (1 / 2) * Real.log (256 * u ^ 2) := by
    rw [Real.log_mul (by linarith : sl ≠ 0) hu0.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have he : (256 : ℝ) = 2 ^ 8 := by norm_num
    rw [he, Real.log_pow]
    have h3 : 0 ≤ Real.log sl := Real.log_nonneg (by linarith)
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    push_cast
    linarith
  have hpi : (3 : ℝ) ≤ Real.pi := (by linarith [Real.pi_gt_d2])
  have hf : 8 ≤ (1 - epsilon) * Real.pi * (sl * u) := by
    have hcoef : (999 / 1000 : ℝ) ≤ 1 - epsilon := by linarith
    have him : (3 : ℝ) ≤ sl * u := by nlinarith
    have hh : (999 / 1000 : ℝ) * 3 * 3 ≤ (1 - epsilon) * Real.pi * (sl * u) := by
      gcongr
    linarith
  change (3 : ℝ) ≤ gAlpha (1 / 2048) epsilon c m (1 / 4) (Unu (1 / 4)) z
  unfold gAlpha
  rw [hIm]
  nlinarith

end CatalanCore.Cert.QuarterContour

#print axioms CatalanCore.Cert.QuarterContour.tail_core
