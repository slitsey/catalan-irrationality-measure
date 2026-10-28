module

public import CatalanCore.Uniform.Decay.Cells.Far
public import CatalanCore.Uniform.Decay.Polygon.Rules
public import CatalanCore.Uniform.Decay.Spline.PolyBridge

@[expose] public section

/-!
# Mass cancellation: `FarHyp` from a statement about `Vnu` alone (lane D, package D6)

For the trial measure `σ` (nonnegative densities, mass one, support in the disc of radius `Rc`)
and `‖z‖ ≥ 2 Rc`, `|U0 z + log ‖z‖| ≤ 2 Rc / ‖z‖` (`U0_far`).  Hence the hypothesis
`FarHyp` of the far rule follows from the corresponding far-field statement
`|Vnu z + M log ‖z‖| ≤ 2 N₁ / ‖z‖` for the second potential only (`farHyp_of_nu`), with
`M₁ = M Rc + N₁`.
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline

variable {D : SplineData}

theorem pt_norm_le (B : SplineData.BasicFacts D) (i : Fin D.n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖pt D.A D.B i t‖ ≤ (D.Rc : ℝ) := by
  have : pt D.A D.B i t = ((1 - t : ℝ) : ℂ) * D.A i + (t : ℂ) * D.B i := by
    unfold pt; push_cast; ring
  rw [this]
  calc ‖((1 - t : ℝ) : ℂ) * D.A i + (t : ℂ) * D.B i‖
      ≤ ‖((1 - t : ℝ) : ℂ) * D.A i‖ + ‖(t : ℂ) * D.B i‖ := norm_add_le _ _
    _ = (1 - t) * ‖D.A i‖ + t * ‖D.B i‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ (1 - t) * (D.Rc : ℝ) + t * (D.Rc : ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (B.hAR i) (by linarith))
          (mul_le_mul_of_nonneg_left (B.hBR i) h0)
    _ = D.Rc := by ring

theorem mass_one (B : SplineData.BasicFacts D) : ∑ i, ∫ t in (0 : ℝ)..1, D.f i t = 1 := by
  have := B.hmass
  simp_rw [SplineData.f, integral_ratPoly]
  rw [← Rat.cast_sum]
  exact_mod_cast this

/-- **Far field of the trial potential.** -/
theorem U0_far (B : SplineData.BasicFacts D) {z : ℂ} (hz0 : 0 < ‖z‖) (hz : 2 * (D.Rc : ℝ) ≤ ‖z‖) :
    |U0 D.A D.B D.f z + Real.log ‖z‖| ≤ 2 * (D.Rc : ℝ) / ‖z‖ := by
  have hpt : ∀ (i : Fin D.n) (t : ℝ), 0 ≤ t → t ≤ 1 →
      |-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖| ≤ 2 * (D.Rc : ℝ) / ‖z‖ := by
    intro i t h0 h1
    have hp := pt_norm_le B i h0 h1
    set p := pt D.A D.B i t
    have hζ : ‖p / z‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ hz0]; linarith
    have hz' : z ≠ 0 := norm_pos_iff.1 hz0
    have e : ‖z - p‖ = ‖z‖ * ‖1 - p / z‖ := by
      rw [← norm_mul]; congr 1; field_simp
    have hpos : 0 < ‖1 - p / z‖ := by
      have h3 : 1 - ‖p / z‖ ≤ ‖1 - p / z‖ := by
        have := norm_sub_norm_le (1 : ℂ) (p / z); simpa using this
      linarith
    have hl : Real.log ‖z - p‖ = Real.log ‖z‖ + Real.log ‖1 - p / z‖ := by
      rw [e, Real.log_mul hz0.ne' hpos.ne']
    have := CatalanCore.Uniform.Decay.Polygon.abs_log_norm_one_sub_le hζ
    rw [hl]
    have e2 : -(Real.log ‖z‖ + Real.log ‖1 - p / z‖) + Real.log ‖z‖ = -Real.log ‖1 - p / z‖ := by ring
    rw [e2, abs_neg]
    refine this.trans ?_
    rw [norm_div]
    calc 2 * (‖p‖ / ‖z‖) = 2 * ‖p‖ / ‖z‖ := by ring
      _ ≤ 2 * (D.Rc : ℝ) / ‖z‖ := by gcongr
  have hne : ∀ (i : Fin D.n) (t : ℝ), 0 ≤ t → t ≤ 1 → ‖z - pt D.A D.B i t‖ ≠ 0 := by
    intro i t h0 h1 h
    have hp := pt_norm_le B i h0 h1
    have h2 : ‖z‖ - ‖pt D.A D.B i t‖ ≤ ‖z - pt D.A D.B i t‖ := norm_sub_norm_le z _
    have := B.hRc
    linarith
  have hint : ∀ i : Fin D.n, IntervalIntegrable
      (fun t => D.f i t * (-Real.log ‖z - pt D.A D.B i t‖)) volume 0 1 := by
    intro i
    refine ContinuousOn.intervalIntegrable ?_
    refine (density_cont i).continuousOn.mul ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hc : Continuous (fun t => z - pt D.A D.B i t) := continuous_const.sub (continuous_pt D.A D.B i)
    exact ((hc.norm.continuousAt.log (hne i t ht.1 ht.2)).neg).continuousWithinAt
  have hsplit : U0 D.A D.B D.f z + Real.log ‖z‖ =
      ∑ i, ∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖) := by
    have h1 : ∀ i : Fin D.n, ∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖)
        = (∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖)) +
          Real.log ‖z‖ * ∫ t in (0 : ℝ)..1, D.f i t := by
      intro i
      simp_rw [mul_add]
      rw [integral_add (hint i) ((density_cont i).intervalIntegrable _ _ |>.mul_const _),
        intervalIntegral.integral_mul_const]
      ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, mass_one B]
    unfold U0; ring
  have hb : ∀ i : Fin D.n, |∫ t in (0 : ℝ)..1,
      D.f i t * (-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖)| ≤
      (2 * (D.Rc : ℝ) / ‖z‖) * ∫ t in (0 : ℝ)..1, D.f i t := by
    intro i
    rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ ?_
    · refine Filter.Eventually.of_forall fun t ht => ?_
      have hf := density_bounds B i t ht.1.le ht.2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hf.1]
      rw [mul_comm (2 * (D.Rc : ℝ) / ‖z‖)]
      exact mul_le_mul_of_nonneg_left (hpt i t ht.1.le ht.2) hf.1
    · exact ((density_cont i).intervalIntegrable _ _).const_mul _
  rw [hsplit]
  calc |∑ i, ∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖)|
      ≤ ∑ i, |∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖ + Real.log ‖z‖)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin D.n, (2 * (D.Rc : ℝ) / ‖z‖) * ∫ t in (0 : ℝ)..1, D.f i t :=
        Finset.sum_le_sum fun i _ => hb i
    _ = 2 * (D.Rc : ℝ) / ‖z‖ := by rw [← Finset.mul_sum, mass_one B, mul_one]

/-- Far constants from the far field of `Vnu` alone. -/
theorem farHyp_of_nu {Vnu : ℂ → ℝ} (B : SplineData.BasicFacts D) (F : FarData) {N1 : ℚ}
    (hN1 : 0 ≤ N1) (hM1 : F.M1 = D.Mq * D.Rc + N1) (hT0 : 0 < F.T0)
    (hT : 2 * D.Rc ≤ F.T0)
    (hV : ∀ z : ℂ, (F.T0 : ℝ) ≤ ‖z‖ →
      |Vnu z + (D.Mq : ℝ) * Real.log ‖z‖| ≤ 2 * (N1 : ℝ) / ‖z‖) :
    FarHyp D Vnu F := by
  refine ⟨?_, hT0, fun z hz => ?_⟩
  · rw [hM1]
    have := B.hM
    have h0 : 0 ≤ D.Rc := by exact_mod_cast B.hRc
    positivity
  · have hT0R : (0 : ℝ) < F.T0 := by exact_mod_cast hT0
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hT0R hz
    have hTR : 2 * (D.Rc : ℝ) ≤ F.T0 := by exact_mod_cast hT
    have h1 := U0_far B hz0 (hTR.trans hz)
    have h2 := hV z hz
    have hMq : (0 : ℝ) < D.Mq := by exact_mod_cast B.hM
    have e : (D.Mq : ℝ) * U0 D.A D.B D.f z - Vnu z =
        (D.Mq : ℝ) * (U0 D.A D.B D.f z + Real.log ‖z‖) - (Vnu z + (D.Mq : ℝ) * Real.log ‖z‖) := by ring
    rw [e]
    have e2 : 2 * (F.M1 : ℝ) / ‖z‖ = (D.Mq : ℝ) * (2 * (D.Rc : ℝ) / ‖z‖) + 2 * (N1 : ℝ) / ‖z‖ := by
      rw [hM1]; push_cast; field_simp
    rw [e2]
    calc |(D.Mq : ℝ) * (U0 D.A D.B D.f z + Real.log ‖z‖) - (Vnu z + (D.Mq : ℝ) * Real.log ‖z‖)|
        ≤ |(D.Mq : ℝ) * (U0 D.A D.B D.f z + Real.log ‖z‖)| +
          |Vnu z + (D.Mq : ℝ) * Real.log ‖z‖| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos hMq]
        gcongr

end CatalanCore.Uniform.Decay.Cells
