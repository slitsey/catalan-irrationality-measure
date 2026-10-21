module

public import CatalanCore.Cert.SigmaQuarter.Potential
public import CatalanCore.Decay.Rect.CertG
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Real MeasureTheory intervalIntegral

namespace CatalanCore.Cert.SigmaQuarter

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

theorem tail_core {K : ℕ} (c : Fin K → ℂ) (m : Fin K → ℝ)
    (hm : ∀ k, 0 ≤ m k) (hsum : ∑ k, m k = 1) (hn : ∀ k, ‖c k‖ ≤ 16)
    (u δ : ℝ) (hu : (3 / 2 : ℝ) ≤ u) (hδ : |δ| ≤ 1 / 2 ^ 30) :
    (11571 / 5000 : ℝ) ≤
      gAlpha (1 / 2048) (1 / 1000) c m (1 / 4) (Unu (1 / 4))
        ⟨-(1 / 10 : ℝ) + δ - u, 3 * u⟩ := by
  have hu0 : 0 < u := by linarith
  set z : ℂ := ⟨-(1 / 10 : ℝ) + δ - u, 3 * u⟩ with hz
  have hd := abs_le.mp (hδ.trans (by norm_num : (1 / 2 ^ 30 : ℝ) ≤ 1 / 100))
  have hr : z.re ^ 2 ≤ (u + 1 / 8) ^ 2 := by
    apply sq_le_sq'
    · dsimp [z]; linarith
    · dsimp [z]; linarith
  have hzs : ‖z‖ ^ 2 ≤ 16 * u ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him : z.im = 3 * u := rfl
    rw [him]
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
  have hIm : |z.im| = 3 * u := abs_of_pos (by change 0 < 3 * u; positivity)
  have hUn := Unu_upper z (α := 1 / 4) (by norm_num) (by rw [hIm]; positivity)
  rw [hIm] at hUn
  have hlog : -(4 : ℝ) ≤ Real.log (3 * u) - (1 / 2) * Real.log (256 * u ^ 2) := by
    rw [Real.log_mul (by norm_num) hu0.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have he : (256 : ℝ) = 2 ^ 8 := by norm_num
    rw [he, Real.log_pow]
    have h3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    push_cast
    linarith
  have hpi : (3 : ℝ) ≤ Real.pi := (by linarith [Real.pi_gt_d2])
  have hf : 13 ≤ (999 / 1000 : ℝ) * Real.pi * (3 * u) := by
    have : (999 / 1000 : ℝ) * 3 * (3 * u) ≤ (999 / 1000 : ℝ) * Real.pi * (3 * u) := by gcongr
    nlinarith
  change (11571 / 5000 : ℝ) ≤ gAlpha (1 / 2048) (1 / 1000) c m (1 / 4) (Unu (1 / 4)) z
  unfold gAlpha
  rw [hIm]
  nlinarith

end CatalanCore.Cert.SigmaQuarter
