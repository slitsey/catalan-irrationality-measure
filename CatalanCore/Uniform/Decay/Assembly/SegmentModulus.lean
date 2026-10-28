module

public import CatalanCore.Uniform.Decay.Assembly.LogModulusAbs
public import CatalanCore.Uniform.Decay.Spline.Smooth

@[expose] public section

/-!
# The log-modulus theorem for a segment potential (lane D, package D5a)

For the segment `pt t = A + t (B - A)`, `L = ‖B - A‖ > 0`, a continuous density `f` with
`|f| ≤ M` on `[0,1]` (arclength density `M / L`), and `0 < δ ≤ 1/4`, `‖z - z'‖ ≤ δ`:

`|∫₀¹ f (-log ‖z - pt‖) - ∫₀¹ f (-log ‖z' - pt‖)|
    ≤ (M / L) · δ · (17 + 14 |log δ| + 3 log (1 + L / (3 δ)))`.

This is the potential modulus used for the endpoint / support-intersection cells of the
finite certificate checker.  Since `log (1 + L/(3δ)) ≤ log (1 + L/(2δ))`, it implies the
paper's form `F δ (c₁ + c₂ |log δ| + c₃ log (1 + L/(2δ)))` with `(c₁, c₂, c₃) = (17, 14, 4)`.
-/

namespace CatalanCore.Uniform.Decay.Assembly

open MeasureTheory Set intervalIntegral CatalanCore.Uniform.Decay.Spline

/-- The segment-potential integrand pair differs by at most the modulus (the integral of the
absolute difference of logarithms). -/
theorem segment_abs_log_diff_le {A B : ℂ} (hAB : A ≠ B) {z z' : ℂ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (hzz : ‖z - z'‖ ≤ δ) :
    ∫ t in (0 : ℝ)..1, |Real.log ‖z - (A + (t : ℂ) * (B - A))‖
        - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖|
      ≤ ‖B - A‖⁻¹ * (δ * (17 + 14 * |Real.log δ|
          + 3 * Real.log (1 + ‖B - A‖ / (3 * δ)))) := by
  set L : ℝ := ‖B - A‖ with hL
  have hL0 : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  set ζ : ℂ := (z - A) / (B - A) with hζ
  set ζ' : ℂ := (z' - A) / (B - A) with hζ'
  set g : ℝ → ℝ := fun t => |Real.log ‖z - (A + (t : ℂ) * (B - A))‖
        - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖| with hg
  have hscale : ∫ s in (0 : ℝ)..L, g (s / L) = L • ∫ t in (0 : ℝ)..1, g t := by
    have := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := L) g hL0.ne'
    rw [this]; simp [div_self hL0.ne']
  have hmain := integral_abs_log_diff_le (a := fun s => ‖z - (A + ((s / L : ℝ) : ℂ) * (B - A))‖)
    (b := fun s => ‖z' - (A + ((s / L : ℝ) : ℂ) * (B - A))‖) (x := L * ζ.re) (x' := L * ζ'.re)
    (δ := δ) (L := L) hδ0 hδ hL0.le ?_ ?_ ?_ ?_
  · rw [← integral_of_le hL0.le] at hmain
    have e : ∫ s in (0 : ℝ)..L, g (s / L) = ∫ s in (0 : ℝ)..L,
        |Real.log ‖z - (A + ((s / L : ℝ) : ℂ) * (B - A))‖
          - Real.log ‖z' - (A + ((s / L : ℝ) : ℂ) * (B - A))‖| := rfl
    rw [e] at hscale
    have h2 : L • ∫ t in (0 : ℝ)..1, g t ≤ δ * (17 + 14 * |Real.log δ|
        + 3 * Real.log (1 + L / (3 * δ))) := by rw [← hscale]; exact hmain
    rw [smul_eq_mul] at h2
    have : ∫ t in (0 : ℝ)..1, g t = L⁻¹ * (L * ∫ t in (0 : ℝ)..1, g t) := by
      field_simp
    show ∫ t in (0 : ℝ)..1, g t ≤ _
    rw [this]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hL0.le)
  · -- |x - x'| ≤ δ
    have h1 : ζ - ζ' = (z - z') / (B - A) := by
      rw [hζ, hζ']; field_simp; ring
    have h2 : |ζ.re - ζ'.re| ≤ ‖z - z'‖ / L := by
      calc |ζ.re - ζ'.re| = |(ζ - ζ').re| := by simp
        _ ≤ ‖ζ - ζ'‖ := Complex.abs_re_le_norm _
        _ = ‖z - z'‖ / L := by rw [h1, norm_div]
    have h3 : |L * ζ.re - L * ζ'.re| = L * |ζ.re - ζ'.re| := by
      rw [← mul_sub, abs_mul, abs_of_pos hL0]
    rw [h3]
    calc L * |ζ.re - ζ'.re| ≤ L * (‖z - z'‖ / L) := mul_le_mul_of_nonneg_left h2 hL0.le
      _ = ‖z - z'‖ := by field_simp
      _ ≤ δ := hzz
  · intro s hs
    have := dist_ge z A B hAB (s / L)
    have e : |s - L * ζ.re| = L * |ζ.re - s / L| := by
      have : s - L * ζ.re = -(L * (ζ.re - s / L)) := by field_simp; ring
      rw [this, abs_neg, abs_mul, abs_of_pos hL0]
    rw [e]; exact this
  · intro s hs
    have := dist_ge z' A B hAB (s / L)
    have e : |s - L * ζ'.re| = L * |ζ'.re - s / L| := by
      have : s - L * ζ'.re = -(L * (ζ'.re - s / L)) := by field_simp; ring
      rw [this, abs_neg, abs_mul, abs_of_pos hL0]
    rw [e]; exact this
  · intro s hs
    have := abs_norm_sub_norm_le (z - (A + ((s / L : ℝ) : ℂ) * (B - A)))
      (z' - (A + ((s / L : ℝ) : ℂ) * (B - A)))
    have e : z - (A + ((s / L : ℝ) : ℂ) * (B - A)) - (z' - (A + ((s / L : ℝ) : ℂ) * (B - A)))
        = z - z' := by ring
    rw [e] at this
    exact this.trans hzz

/-- **Log-modulus theorem for a segment potential.** -/
theorem segment_log_modulus {A B : ℂ} (hAB : A ≠ B) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M) {z z' : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hzz : ‖z - z'‖ ≤ δ) :
    |(∫ t in (0 : ℝ)..1, f t * (-Real.log ‖z - (A + (t : ℂ) * (B - A))‖))
        - ∫ t in (0 : ℝ)..1, f t * (-Real.log ‖z' - (A + (t : ℂ) * (B - A))‖)|
      ≤ (M / ‖B - A‖) * (δ * (17 + 14 * |Real.log δ|
          + 3 * Real.log (1 + ‖B - A‖ / (3 * δ)))) := by
  have hL0 : 0 < ‖B - A‖ := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have i1 := intervalIntegrable_log_dist z A B hAB
  have i2 := intervalIntegrable_log_dist z' A B hAB
  have j1 : IntervalIntegrable (fun t : ℝ => f t * (-Real.log ‖z - (A + (t : ℂ) * (B - A))‖))
      volume 0 1 := i1.neg.continuousOn_mul hf.continuousOn
  have j2 : IntervalIntegrable (fun t : ℝ => f t * (-Real.log ‖z' - (A + (t : ℂ) * (B - A))‖))
      volume 0 1 := i2.neg.continuousOn_mul hf.continuousOn
  rw [← intervalIntegral.integral_sub j1 j2]
  have hint : IntervalIntegrable (fun t : ℝ => M * |Real.log ‖z - (A + (t : ℂ) * (B - A))‖
        - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖|) volume 0 1 :=
    (i1.sub i2).abs.const_mul M
  have hle := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t : ℝ => f t * (-Real.log ‖z - (A + (t : ℂ) * (B - A))‖)
        - f t * (-Real.log ‖z' - (A + (t : ℂ) * (B - A))‖))
    (g := fun t : ℝ => M * |Real.log ‖z - (A + (t : ℂ) * (B - A))‖
        - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖|)
    (Filter.Eventually.of_forall (fun t ht => by
      simp only [Real.norm_eq_abs]
      have e : f t * (-Real.log ‖z - (A + (t : ℂ) * (B - A))‖)
          - f t * (-Real.log ‖z' - (A + (t : ℂ) * (B - A))‖)
          = - (f t * (Real.log ‖z - (A + (t : ℂ) * (B - A))‖
              - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖)) := by ring
      rw [e, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM t ⟨ht.1.le, ht.2⟩) (abs_nonneg _))) hint
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have := segment_abs_log_diff_le hAB hδ0 hδ hzz
  calc M * ∫ t in (0 : ℝ)..1, |Real.log ‖z - (A + (t : ℂ) * (B - A))‖
          - Real.log ‖z' - (A + (t : ℂ) * (B - A))‖|
      ≤ M * (‖B - A‖⁻¹ * (δ * (17 + 14 * |Real.log δ|
          + 3 * Real.log (1 + ‖B - A‖ / (3 * δ))))) := mul_le_mul_of_nonneg_left this hM0
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The form with the paper's constants `(17, 14, 4)`: weaken `3 log(1 + L/(3δ))` to
`4 log (1 + L/(2δ))`. -/
theorem segment_log_modulus_paper {A B : ℂ} (hAB : A ≠ B) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M) {z z' : ℂ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (hzz : ‖z - z'‖ ≤ δ) :
    |(∫ t in (0 : ℝ)..1, f t * (-Real.log ‖z - (A + (t : ℂ) * (B - A))‖))
        - ∫ t in (0 : ℝ)..1, f t * (-Real.log ‖z' - (A + (t : ℂ) * (B - A))‖)|
      ≤ (M / ‖B - A‖) * (δ * (17 + 14 * |Real.log δ|
          + 4 * Real.log (1 + ‖B - A‖ / (2 * δ)))) := by
  have hL0 : 0 < ‖B - A‖ := norm_pos_iff.2 (sub_ne_zero.2 hAB.symm)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine (segment_log_modulus hAB hf hM hδ0 hδ hzz).trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hM0 hL0.le)
  apply mul_le_mul_of_nonneg_left _ hδ0.le
  have h1 : Real.log (1 + ‖B - A‖ / (3 * δ)) ≤ Real.log (1 + ‖B - A‖ / (2 * δ)) := by
    apply Real.log_le_log (by have : 0 ≤ ‖B - A‖ / (3 * δ) := by positivity
                              linarith)
    have : ‖B - A‖ / (3 * δ) ≤ ‖B - A‖ / (2 * δ) :=
      div_le_div_of_nonneg_left hL0.le (by positivity) (by linarith)
    linarith
  have h0 : 0 ≤ Real.log (1 + ‖B - A‖ / (3 * δ)) :=
    Real.log_nonneg (by have : 0 ≤ ‖B - A‖ / (3 * δ) := by positivity
                        linarith)
  linarith

end CatalanCore.Uniform.Decay.Assembly
