module

public import CatalanCore.Uniform.Decay.Spline.SmoothLog
public import CatalanCore.Uniform.Decay.Spline.Midpoint

@[expose] public section

/-!
# Fixed-ρ smoothing of the logarithmic potential of a segment-polynomial density (lane D, D2)

For a piece `pt t = A + t (B - A)`, `L = ‖B - A‖ > 0`, a continuous density `f` with `|f| ≤ M` on `[0,1]`:

* `intervalIntegrable_log_dist` : `t ↦ log ‖z - pt t‖` is integrable on `[0,1]`, for every `z`.
* `piece_smooth` : `|∫₀¹ f (log‖z-pt‖ - (1/2) log(‖z-pt‖²+ρ²))| ≤ M π ρ / L`.
* `U0`, `Urho` and `smooth_err` : `|U0 z - Urho z| ≤ π ρ B` with `B = ∑ M_i / L_i`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral Set MeasureTheory CatalanLambda.Decay

section Piece

variable {A B : ℂ}

theorem pt_sub (z A B : ℂ) (hAB : A ≠ B) (t : ℝ) :
    z - (A + (t : ℂ) * (B - A)) = (B - A) * ((z - A) / (B - A) - (t : ℂ)) := by
  have : B - A ≠ 0 := sub_ne_zero.2 hAB.symm
  field_simp
  ring

theorem dist_ge (z A B : ℂ) (hAB : A ≠ B) (t : ℝ) :
    ‖B - A‖ * |((z - A) / (B - A)).re - t| ≤ ‖z - (A + (t : ℂ) * (B - A))‖ := by
  rw [pt_sub z A B hAB, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have := Complex.abs_re_le_norm ((z - A) / (B - A) - (t : ℂ))
  simpa using this

theorem dist_le (z A B : ℂ) (hAB : A ≠ B) (t : ℝ) :
    ‖z - (A + (t : ℂ) * (B - A))‖
      ≤ ‖B - A‖ * (|((z - A) / (B - A)).re - t| + |((z - A) / (B - A)).im|) := by
  rw [pt_sub z A B hAB, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have := Complex.norm_le_abs_re_add_abs_im ((z - A) / (B - A) - (t : ℂ))
  simpa using this

theorem intervalIntegrable_log_dist (z A B : ℂ) (hAB : A ≠ B) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖z - (A + (t : ℂ) * (B - A))‖) volume 0 1 := by
  set ζ : ℂ := (z - A) / (B - A) with hζ
  set t0 : ℝ := ζ.re with ht0
  set L : ℝ := ‖B - A‖ with hL
  have hL0 : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  set C : ℝ := L * (1 + |t0| + |ζ.im|) with hC
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hg : IntegrableOn (fun t : ℝ => |Real.log L| + |Real.log C| + |Real.log (t - t0)|)
      (Ioc (0 : ℝ) 1) volume := by
    have h1 : IntervalIntegrable (fun t : ℝ => Real.log (t - t0)) volume 0 1 := by
      have := (intervalIntegrable_log' (a := (0 : ℝ) - t0) (b := 1 - t0)).comp_sub_right t0
      simpa using this
    have h2 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h1).abs
    exact (integrableOn_const (by simp)).add h2
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.log ‖z - (A + (t : ℂ) * (B - A))‖)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply Measurable.aestronglyMeasurable
    exact Real.measurable_log.comp (by fun_prop)
  refine Integrable.mono' hg hmeas ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({t0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (by simp)
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with t ht ht1
  have htt : t ≠ t0 := fun h => ht (by simp [h])
  have hpos : 0 < |t0 - t| := abs_pos.2 (sub_ne_zero.2 (Ne.symm htt))
  have hlow := dist_ge z A B hAB t
  have hup := dist_le z A B hAB t
  have hlowpos : 0 < L * |t0 - t| := mul_pos hL0 hpos
  have hdpos : 0 < ‖z - (A + (t : ℂ) * (B - A))‖ := lt_of_lt_of_le hlowpos hlow
  have hlog1 : Real.log (L * |t0 - t|) ≤ Real.log ‖z - (A + (t : ℂ) * (B - A))‖ :=
    Real.log_le_log hlowpos hlow
  have hab : |t0 - t| ≤ 1 + |t0| := by
    have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2]
    calc |t0 - t| ≤ |t0| + |t| := abs_sub _ _
      _ ≤ 1 + |t0| := by linarith
  have hupb : ‖z - (A + (t : ℂ) * (B - A))‖ ≤ C := by
    refine hup.trans ?_
    rw [hC]
    apply mul_le_mul_of_nonneg_left _ hL0.le
    linarith [abs_nonneg ζ.im]
  have hlog2 : Real.log ‖z - (A + (t : ℂ) * (B - A))‖ ≤ Real.log C := Real.log_le_log hdpos hupb
  have e1 : Real.log (L * |t0 - t|) = Real.log L + Real.log (t - t0) := by
    rw [Real.log_mul hL0.ne' hpos.ne', abs_sub_comm, Real.log_abs]
  rw [Real.norm_eq_abs, abs_le]
  have := neg_abs_le (Real.log L)
  have := le_abs_self (Real.log C)
  have := neg_abs_le (Real.log (t - t0))
  have := le_abs_self (Real.log L)
  have := le_abs_self (Real.log (t - t0))
  have := abs_nonneg (Real.log C)
  have := neg_abs_le (Real.log C)
  have := abs_nonneg (Real.log L)
  have := abs_nonneg (Real.log (t - t0))
  constructor <;> linarith

theorem wfun_eq {ρ d : ℝ} (hρ : 0 < ρ) (hd : 0 < d) :
    (1 / 2) * Real.log (d ^ 2 + ρ ^ 2) - Real.log d = (1 / 2) * Real.log (1 + ρ ^ 2 / d ^ 2) := by
  have h1 : Real.log (d ^ 2) = 2 * Real.log d := by rw [Real.log_pow]; norm_num
  have h2 : d ^ 2 + ρ ^ 2 = d ^ 2 * (1 + ρ ^ 2 / d ^ 2) := by field_simp
  have h3 : Real.log (d ^ 2 + ρ ^ 2) = Real.log (d ^ 2) + Real.log (1 + ρ ^ 2 / d ^ 2) := by
    rw [h2]; exact Real.log_mul (by positivity) (by positivity)
  linarith

theorem wfun_nonneg {ρ d : ℝ} (hρ : 0 < ρ) (hd : 0 < d) :
    0 ≤ (1 / 2) * Real.log (d ^ 2 + ρ ^ 2) - Real.log d := by
  rw [wfun_eq hρ hd]
  have : 0 ≤ Real.log (1 + ρ ^ 2 / d ^ 2) := Real.log_nonneg (by have : 0 ≤ ρ ^ 2 / d ^ 2 := by positivity
                                                                 linarith)
  linarith

theorem w_le_phiM {ρ L d u : ℝ} (hρ : 0 < ρ) (hL : 0 < L) (hu : u ≠ 0) (hd : L * |u| ≤ d) :
    (1 / 2) * Real.log (d ^ 2 + ρ ^ 2) - Real.log d ≤ phiM (ρ / L) u := by
  have hu0 : 0 < |u| := abs_pos.2 hu
  have hd0 : 0 < d := lt_of_lt_of_le (mul_pos hL hu0) hd
  have ha : 0 < ρ / L := by positivity
  have e : phiM (ρ / L) u = (1 / 2) * Real.log (|u| ^ 2 + (ρ / L) ^ 2) - Real.log |u| := by
    unfold phiM; rw [sq_abs, Real.log_abs]
  rw [e, wfun_eq hρ hd0, wfun_eq ha hu0]
  have h1 : ρ ^ 2 / d ^ 2 ≤ (ρ / L) ^ 2 / |u| ^ 2 := by
    have h2 : (L * |u|) ^ 2 ≤ d ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hd
    calc ρ ^ 2 / d ^ 2 ≤ ρ ^ 2 / (L * |u|) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      _ = (ρ / L) ^ 2 / |u| ^ 2 := by field_simp
  have h3 : 0 < 1 + ρ ^ 2 / d ^ 2 := by positivity
  have := Real.log_le_log h3 (by linarith : 1 + ρ ^ 2 / d ^ 2 ≤ 1 + (ρ / L) ^ 2 / |u| ^ 2)
  linarith

/-- **One piece**: the smoothing error of a segment potential. -/
theorem piece_smooth (z A B : ℂ) (hAB : A ≠ B) {ρ : ℝ} (hρ : 0 < ρ) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M) :
    |∫ t in (0 : ℝ)..1, f t * ((1 / 2) * Real.log (‖z - (A + (t : ℂ) * (B - A))‖ ^ 2 + ρ ^ 2)
        - Real.log ‖z - (A + (t : ℂ) * (B - A))‖)| ≤ M * (Real.pi * ρ / ‖B - A‖) := by
  set ζ : ℂ := (z - A) / (B - A) with hζ
  set t0 : ℝ := ζ.re with ht0
  set L : ℝ := ‖B - A‖ with hL
  have hL0 : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have ha : 0 < ρ / L := by positivity
  set w : ℝ → ℝ := fun t => (1 / 2) * Real.log (‖z - (A + (t : ℂ) * (B - A))‖ ^ 2 + ρ ^ 2)
        - Real.log ‖z - (A + (t : ℂ) * (B - A))‖ with hw
  have hwint : IntervalIntegrable w volume 0 1 := by
    have h1 : Continuous (fun t : ℝ => (1 / 2) * Real.log (‖z - (A + (t : ℂ) * (B - A))‖ ^ 2 + ρ ^ 2)) :=
      continuous_const.mul (Continuous.log (by fun_prop) (fun x => by positivity))
    exact (h1.intervalIntegrable _ _).sub (intervalIntegrable_log_dist z A B hAB)
  have hgint : IntervalIntegrable (fun t : ℝ => M * phiM (ρ / L) (t0 - t)) volume 0 1 := by
    have := (intervalIntegrable_phiM ha (t0 - 1) t0)
    have h2 := this.comp_sub_left t0
    have h3 : IntervalIntegrable (fun t : ℝ => phiM (ρ / L) (t0 - t)) volume 0 1 := by
      simpa using h2.symm
    exact h3.const_mul M
  have hmain := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => f t * w t) (g := fun t : ℝ => M * phiM (ρ / L) (t0 - t)) ?_ hgint
  · rw [Real.norm_eq_abs] at hmain
    refine hmain.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hc := intervalIntegral.integral_comp_sub_left (fun u => phiM (ρ / L) u) (a := 0) (b := 1) t0
    simp only [sub_zero] at hc
    rw [hc]
    have := integral_phiM_le ha (p := t0 - 1) (q := t0) (by linarith)
    calc M * ∫ x in (t0 - 1)..t0, phiM (ρ / L) x ≤ M * (Real.pi * (ρ / L)) :=
          mul_le_mul_of_nonneg_left this hM0
      _ = M * (Real.pi * ρ / L) := by ring
  · have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({t0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (by simp)
    filter_upwards [hne] with t ht ht1
    have htt : t ≠ t0 := fun h => ht (by simp [h])
    have hu : t0 - t ≠ 0 := sub_ne_zero.2 (Ne.symm htt)
    have hlow := dist_ge z A B hAB t
    have hlowpos : 0 < L * |t0 - t| := mul_pos hL0 (abs_pos.2 hu)
    have hdpos : 0 < ‖z - (A + (t : ℂ) * (B - A))‖ := lt_of_lt_of_le hlowpos hlow
    have h1 := wfun_nonneg hρ hdpos
    have h2 := w_le_phiM hρ hL0 hu hlow
    have ht2 : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    exact mul_le_mul (hM t ht2) h2 h1 hM0

end Piece

end CatalanCore.Uniform.Decay.Spline
