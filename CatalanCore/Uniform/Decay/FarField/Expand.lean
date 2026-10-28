import CatalanCore.Uniform.Decay.FarField.Series
import CatalanCore.Uniform.Decay.FarField.Moments
set_option Elab.async false

/-!
# Far-field expansion of one weighted segment (lane D, package D15)

For a piece `P` (density polynomial `dens`, segment `A → B`), centre `c`, radius `R` with
`‖A - c‖, ‖B - c‖ ≤ R`, and `z` with `‖z - c‖ ≥ r0 > R`:
`Φ_P(z) = mass · log‖z-c‖ - Re ∑_{k=1}^K m_k / (k (z-c)^k) + error`,
`|error| ≤ absM(dens) · ρ^(K+1) / ((K+1)(1-ρ))`, `ρ = R/r0`.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.NearCells

/-- A bound for `∫_0^1 |dens|`: the mass when the density is certified non-negative (Bernstein),
else the `ℓ¹` norm of its monomial coefficients weighted by `1/(i+1)`. -/
def absM (a : List ℚ) : ℚ :=
  if bernLoOk (coeffs a) (a.length - 1) 0 1 0 = true then Tm a 0
  else ∑ i ∈ range (a.length - 1 + 1), |coeffs a i| / ((i : ℚ) + 1)

theorem integral_abs_dens_le (a : List ℚ) :
    ∫ t in (0 : ℝ)..1, |ratPoly a t| ≤ (absM a : ℝ) := by
  unfold absM
  split_ifs with h
  · have hnn : Set.EqOn (fun t => |ratPoly a t|) (fun t => ratPoly a t) (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      apply abs_of_nonneg
      have := bernLoOk_sound_real (a := coeffs a) (d := a.length - 1) (u := 0) (w := 1)
        (lo := 0) one_pos h (x := t) (by simpa using ht.1) (by simpa using ht.2)
      simpa [ratPoly, peval] using this
    rw [intervalIntegral.integral_congr hnn]
    have := integral_dens_pow a 0
    simp only [pow_zero, mul_one] at this
    rw [this]
  · have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |ratPoly a t| ≤
        ∑ i ∈ range (a.length - 1 + 1), |((coeffs a i : ℚ) : ℝ)| * t ^ i := by
      intro t ht
      unfold ratPoly
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 i)]
    have hint1 : IntervalIntegrable (fun t => |ratPoly a t|) MeasureTheory.volume 0 1 :=
      (continuous_ratPoly a).abs.intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t : ℝ => ∑ i ∈ range (a.length - 1 + 1),
        |((coeffs a i : ℚ) : ℝ)| * t ^ i) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => ∑ i ∈ range (a.length - 1 + 1),
        |((coeffs a i : ℚ) : ℝ)| * t ^ i).intervalIntegrable _ _
    calc ∫ t in (0 : ℝ)..1, |ratPoly a t|
        ≤ ∫ t in (0 : ℝ)..1, ∑ i ∈ range (a.length - 1 + 1), |((coeffs a i : ℚ) : ℝ)| * t ^ i :=
          intervalIntegral.integral_mono_on zero_le_one hint1 hint2 hb
      _ = _ := by
          rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
          push_cast
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [intervalIntegral.integral_const_mul, integral_pow]
          simp; ring

theorem phiW_eq_ratPoly (P : WP) (z : ℂ) :
    PhiW P z = ∫ t in (0 : ℝ)..1, ratPoly P.a t *
      Real.log ‖z - (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC))‖ := rfl

/-- **Far-field expansion of one segment.** -/
theorem phiW_far (P : WP) (c z : ℂ) (R r0 : ℝ) (hA : ‖P.A.toC - c‖ ≤ R) (hB : ‖P.B.toC - c‖ ≤ R)
    (hR0 : 0 ≤ R) (hRr : R < r0) (hz : r0 ≤ ‖z - c‖) (K : ℕ) :
    |PhiW P z - ((Tm P.a 0 : ℝ) * Real.log ‖z - c‖
        - (∑ k ∈ range K, momSem P c (k + 1) / (((k + 1 : ℕ) : ℂ) * (z - c) ^ (k + 1))).re)|
      ≤ (absM P.a : ℝ) * ((R / r0) ^ (K + 1) / ((K + 1) * (1 - R / r0))) := by
  set u : ℂ := z - c with hu_def
  have hr0 : 0 < r0 := by linarith
  have huR : r0 ≤ ‖u‖ := hz
  have hnu : 0 < ‖u‖ := by linarith
  have hu : u ≠ 0 := norm_pos_iff.1 hnu
  set ρ : ℝ := R / r0 with hρ_def
  have hρ1 : ρ < 1 := by rw [hρ_def, div_lt_one hr0]; exact hRr
  have hρ0 : 0 ≤ ρ := div_nonneg hR0 hr0.le
  set pt : ℝ → ℂ := fun t => P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC) with hpt
  have hptc : Continuous pt := by simp only [hpt]; fun_prop
  have hpR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖pt t - c‖ ≤ R := by
    intro t ht
    have e : pt t - c = ((1 - t : ℝ) : ℂ) * (P.A.toC - c) + (t : ℂ) * (P.B.toC - c) := by
      simp only [hpt]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1 - t), abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, norm_nonneg (P.A.toC - c), norm_nonneg (P.B.toC - c)]
  set q : ℝ → ℂ := fun t => (pt t - c) / u with hq_def
  have hqρ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖q t‖ ≤ ρ := by
    intro t ht
    simp only [hq_def, norm_div]
    calc ‖pt t - c‖ / ‖u‖ ≤ R / ‖u‖ := by gcongr; exact hpR t ht
      _ ≤ R / r0 := by gcongr
  set err : ℝ → ℝ := fun t => Real.log ‖z - pt t‖ - Real.log ‖u‖ + (logPart (q t) K).re with herr
  have herr_bd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |err t| ≤ ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) := by
    intro t ht
    have hq1 : ‖q t‖ < 1 := lt_of_le_of_lt (hqρ t ht) hρ1
    have hfac : z - pt t = u * (1 - q t) := by
      have h1 : u * (1 - q t) = u - (pt t - c) := by simp only [hq_def]; field_simp
      rw [h1, hu_def]; ring
    have hn1 : ‖1 - q t‖ ≠ 0 := by
      intro h0
      have := norm_eq_zero.1 h0
      have h2 : q t = 1 := by linear_combination -this
      rw [h2] at hq1; simp at hq1
    have hlog : Real.log ‖z - pt t‖ = Real.log ‖u‖ + Real.log ‖1 - q t‖ := by
      rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hu) hn1]
    have : err t = Real.log ‖1 - q t‖ + (logPart (q t) K).re := by
      simp only [herr]; rw [hlog]; ring
    rw [this]
    exact log_series_tail (hqρ t ht) hρ1 K
  -- continuity facts
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, z - pt t ≠ 0 := by
    intro t ht h0
    have h1 : z - c = pt t - c := by linear_combination h0
    have := hpR t ht
    rw [← h1] at this
    linarith
  have hcontlog : ContinuousOn (fun t : ℝ => Real.log ‖z - pt t‖) (Set.Icc 0 1) :=
    ContinuousOn.log (by fun_prop) (fun t ht => norm_ne_zero_iff.2 (hne t ht))
  have hcontlogPart : Continuous fun t : ℝ => (logPart (q t) K).re := by
    unfold logPart
    simp only [hq_def]
    fun_prop
  have hdens : Continuous fun t : ℝ => ratPoly P.a t := continuous_ratPoly P.a
  have hI1 : IntervalIntegrable (fun t : ℝ => ratPoly P.a t * Real.log ‖z - pt t‖)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hdens.continuousOn.mul hcontlog
  have hI2 : IntervalIntegrable (fun t : ℝ => ratPoly P.a t * Real.log ‖u‖)
      MeasureTheory.volume 0 1 := (hdens.mul continuous_const).intervalIntegrable _ _
  have hI3 : IntervalIntegrable (fun t : ℝ => ratPoly P.a t * (logPart (q t) K).re)
      MeasureTheory.volume 0 1 := (hdens.mul hcontlogPart).intervalIntegrable _ _
  -- the three integrals
  have e1 : ∫ t in (0 : ℝ)..1, ratPoly P.a t * Real.log ‖u‖ = (Tm P.a 0 : ℝ) * Real.log ‖u‖ := by
    rw [intervalIntegral.integral_mul_const]
    have := integral_dens_pow P.a 0
    simp only [pow_zero, mul_one] at this
    rw [this]
  have e2 : ∫ t in (0 : ℝ)..1, ratPoly P.a t * (logPart (q t) K).re
      = (∑ k ∈ range K, momSem P c (k + 1) / (((k + 1 : ℕ) : ℂ) * u ^ (k + 1))).re := by
    have hF : ∀ t : ℝ, ratPoly P.a t * (logPart (q t) K).re
        = Complex.reCLM (∑ k ∈ range K, (1 / (((k + 1 : ℕ) : ℂ) * u ^ (k + 1))) *
            (((ratPoly P.a t : ℝ) : ℂ) * (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC) - c) ^ (k + 1))) := by
      intro t
      simp only [Complex.reCLM_apply]
      rw [← Complex.re_ofReal_mul]
      congr 1
      unfold logPart
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hq_def, hpt, div_pow]
      field_simp
    simp_rw [hF]
    have hint : IntervalIntegrable (fun t : ℝ => ∑ k ∈ range K, (1 / (((k + 1 : ℕ) : ℂ) * u ^ (k + 1))) *
            (((ratPoly P.a t : ℝ) : ℂ) * (P.A.toC + (t : ℂ) * (P.B.toC - P.A.toC) - c) ^ (k + 1)))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      have := hdens
      fun_prop
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    simp only [Complex.reCLM_apply]
    congr 1
    rw [intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable
      have := hdens
      fun_prop)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
    unfold momSem
    ring
  -- assemble
  have hsplit : PhiW P z - ((Tm P.a 0 : ℝ) * Real.log ‖u‖
      - (∑ k ∈ range K, momSem P c (k + 1) / (((k + 1 : ℕ) : ℂ) * u ^ (k + 1))).re)
      = ∫ t in (0 : ℝ)..1, ratPoly P.a t * err t := by
    have : ∀ t : ℝ, ratPoly P.a t * err t = ratPoly P.a t * Real.log ‖z - pt t‖
        - ratPoly P.a t * Real.log ‖u‖ + ratPoly P.a t * (logPart (q t) K).re := by
      intro t; simp only [herr]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hI1.sub hI2) hI3, intervalIntegral.integral_sub hI1 hI2, e1, e2,
      phiW_eq_ratPoly]
    ring
  rw [hsplit]
  have hεnn : 0 ≤ ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hint_err : IntervalIntegrable (fun t : ℝ => |ratPoly P.a t * err t|) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    have h1 : ContinuousOn (fun t : ℝ => ratPoly P.a t * err t) (Set.Icc 0 1) := by
      have : ∀ t : ℝ, ratPoly P.a t * err t = ratPoly P.a t * Real.log ‖z - pt t‖
          - ratPoly P.a t * Real.log ‖u‖ + ratPoly P.a t * (logPart (q t) K).re := by
        intro t; simp only [herr]; ring
      simp_rw [this]
      exact ((hdens.continuousOn.mul hcontlog).sub (hdens.mul continuous_const).continuousOn).add
        (hdens.mul hcontlogPart).continuousOn
    exact h1.abs
  have hint_abs : IntervalIntegrable (fun t : ℝ => ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) * |ratPoly P.a t|)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_ratPoly P.a).abs).intervalIntegrable _ _
  calc |∫ t in (0 : ℝ)..1, ratPoly P.a t * err t|
      ≤ ∫ t in (0 : ℝ)..1, |ratPoly P.a t * err t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) * |ratPoly P.a t| := by
        refine intervalIntegral.integral_mono_on zero_le_one hint_err hint_abs fun t ht => ?_
        rw [abs_mul]
        have := herr_bd t ht
        nlinarith [abs_nonneg (ratPoly P.a t), abs_nonneg (err t)]
    _ = ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) * ∫ t in (0 : ℝ)..1, |ratPoly P.a t| := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ρ ^ (K + 1) / ((K + 1) * (1 - ρ)) * (absM P.a : ℝ) :=
        mul_le_mul_of_nonneg_left (integral_abs_dens_le P.a) hεnn
    _ = _ := by rw [mul_comm]

end CatalanCore.Uniform.Decay.FarField
