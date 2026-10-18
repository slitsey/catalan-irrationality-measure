module

public import CatalanLambda.Mirror.Contour
public import CatalanLambda.Decay.RayDirection

@[expose] public section

/-!
# Mirror constant: exponential decay of `Ē` along the rays `x* + r e^{±iφ}`

`‖Ē(x* + r e^{±iφ})‖ ≤ C · exp(-2π r sin φ)` with the same `C = 16π + π e^{π/4}/(7/16)²`.
Near the vertex both `sin πz` and `sin(πz - 3π/4)` stay at least `7/16` away from `0`.
-/

open Complex Set

namespace CatalanLambda.Mirror

open CatalanLambda.Decay (sin_lb_sym abs_sin_shift rayPt_im rayPt_re phiR phiR_gt phiR_lt phiR_cot
  sin_phiR kap2 kap2_pos rayPt)

theorem ECB_ray_bound_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 5 / 4 * Real.sin φ) (N0 : ℕ) {θ : ℝ} (hθ : θ = φ ∨ θ = -φ) {r : ℝ}
    (hr : 0 ≤ r) :
    ‖ECB (rayPt (xstarB N0) θ r)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin φ))) := by
  have hpi := Real.pi_pos
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hφ2
  have hcφ : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hφ1 (by linarith)
  have hcosθ : Real.cos θ = Real.cos φ := by
    rcases hθ with h | h <;> simp [h]
  have habs : |(rayPt (xstarB N0) θ r).im| = r * Real.sin φ := by
    rw [rayPt_im]
    have : |Real.sin θ| = Real.sin φ := by
      rcases hθ with h | h
      · rw [h]; exact abs_of_pos hsφ
      · rw [h, Real.sin_neg, abs_neg]; exact abs_of_pos hsφ
    rw [abs_mul, abs_of_nonneg hr, this]
  have key := ECB_norm_le_uniform (7 / 16) (by norm_num) (rayPt (xstarB N0) θ r) ?_
  · rw [habs] at key
    exact key
  · by_cases hbig : 1 / 8 ≤ |(rayPt (xstarB N0) θ r).im|
    · exact Or.inl hbig
    · right
      rw [habs] at hbig
      set δ := -(r * Real.cos φ) with hδ
      have hδ0 : 0 ≤ δ := by nlinarith
      have hδ1 : δ ≤ 5 / 32 := by nlinarith [mul_le_mul_of_nonneg_left hcot hr]
      -- π re = -N π + π (3/8 - δ) ;  π re - 3π/4 = -N π - π (3/8 + δ)
      have hre : Real.pi * (rayPt (xstarB N0) θ r).re
          = -(N0 : ℝ) * Real.pi - (-(Real.pi * (3 / 8 - δ))) := by
        rw [rayPt_re, hcosθ, hδ]; unfold xstarB; ring
      have hre2 : Real.pi * (rayPt (xstarB N0) θ r).re - 3 * Real.pi / 4
          = -(N0 : ℝ) * Real.pi - Real.pi * (3 / 8 + δ) := by
        rw [rayPt_re, hcosθ, hδ]; unfold xstarB; ring
      constructor
      · rw [hre2, abs_sin_shift]
        have := sin_lb_sym (y := Real.pi * (3 / 8 + δ)) (c := 7 * Real.pi / 32) (by positivity)
          (by nlinarith) (by nlinarith) (by linarith)
        have e : 2 / Real.pi * (7 * Real.pi / 32) = 7 / 16 := by field_simp; ring
        rw [abs_of_nonneg (by
          have : 0 ≤ Real.sin (Real.pi * (3 / 8 + δ)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith
          exact this)]
        linarith
      · rw [hre, abs_sin_shift, Real.sin_neg, abs_neg]
        have := sin_lb_sym (y := Real.pi * (3 / 8 - δ)) (c := 7 * Real.pi / 32) (by positivity)
          (by nlinarith) (by nlinarith) (by linarith)
        have e : 2 / Real.pi * (7 * Real.pi / 32) = 7 / 16 := by field_simp; ring
        rw [abs_of_nonneg (by
          have : 0 ≤ Real.sin (Real.pi * (3 / 8 - δ)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith
          exact this)]
        linarith

/-- The integrable majorant on the rays. -/
theorem Ev_ray_bound_genB {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 5 / 4 * Real.sin φ) (N0 a b : ℕ) (hN : 1 ≤ N0) {θ : ℝ}
    (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) :
    ‖ECB (rayPt (xstarB N0) θ r) * ((rayPt (xstarB N0) θ r - a)⁻¹ * (rayPt (xstarB N0) θ r - b)⁻¹)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin φ)))
        * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)))) := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hφ2
  have hs : Real.sin θ ≠ 0 := by
    rcases hθ with h | h
    · rw [h]; exact ne_of_gt hsφ
    · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hsφ)
  rw [norm_mul, norm_mul]
  exact mul_le_mul (ECB_ray_bound_gen hφ1 hφ2 hcot N0 hθ hr)
    (mul_le_mul (norm_inv_ray_nat_leB N0 a hN hs hr) (norm_inv_ray_nat_leB N0 b hN hs hr)
      (norm_nonneg _) (by have := Real.sqrt_pos.2 (kap2_pos hs); positivity))
    (by positivity) (by positivity)

theorem contour_identity_RB (N0 a b : ℕ) (hN : 1 ≤ N0) :
    ((16 * TbarEnt a b : ℝ) : ℂ)
      = -((∑ m ∈ Finset.range N0, atomTermB a b m : ℝ) : ℂ)
        - ((1 / (((a : ℝ) + N0) * ((b : ℝ) + N0)) : ℝ) : ℂ)
        + (2 * Real.pi * I)⁻¹ *
          CatalanLambda.Decay.contL (xstarB N0) phiR (fun z => ECB z * ((z - a)⁻¹ * (z - b)⁻¹)) :=
  contour_identity_genB phiR_gt phiR_lt N0 a b hN

theorem ECB_ray_bound_R (N0 : ℕ) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ} (hr : 0 ≤ r) :
    ‖ECB (rayPt (xstarB N0) θ r)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiR))) :=
  ECB_ray_bound_gen phiR_gt phiR_lt phiR_cot N0 hθ hr

theorem Ev_ray_bound_RB (N0 a b : ℕ) (hN : 1 ≤ N0) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ}
    (hr : 0 ≤ r) :
    ‖ECB (rayPt (xstarB N0) θ r) * ((rayPt (xstarB N0) θ r - a)⁻¹ * (rayPt (xstarB N0) θ r - b)⁻¹)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiR)))
        * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)))) :=
  Ev_ray_bound_genB phiR_gt phiR_lt phiR_cot N0 a b hN hθ hr

theorem integrableOn_E_ray_RB (N0 a b : ℕ) (hN : 1 ≤ N0) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) :
    MeasureTheory.IntegrableOn (fun r : ℝ => (ECB (rayPt (xstarB N0) θ r)
      * ((rayPt (xstarB N0) θ r - a)⁻¹ * (rayPt (xstarB N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (Ioi 0) := by
  have hs : 0 < Real.sin phiR := by rw [sin_phiR]; positivity
  apply integrableOn_E_rayB N0 a b hN
  rcases hθ with h | h
  · rw [h]; exact ne_of_gt hs
  · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hs)

end CatalanLambda.Mirror
