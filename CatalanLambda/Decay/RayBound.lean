import CatalanLambda.Decay.Contour
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exponential decay of `E` along the rays `x* + r e^{±iφ}`

`‖E(x* + r e^{±iφ})‖ ≤ C · exp(-2π r sin φ)` with `C = 16π + π e^{π/4}/(7/16)²`, uniformly in `N0`.
Near the vertex (`r sin φ < 1/8`) both `sin πz` and `sin(πz - π/4)` stay at least `7/16` away from `0`.
-/

open Complex Set

namespace CatalanLambda.Decay

lemma sin_lb_sym {y c : ℝ} (hc0 : 0 ≤ c) (h1 : c ≤ y) (h2 : y ≤ Real.pi - c)
    (hcπ : c ≤ Real.pi / 2) : 2 / Real.pi * c ≤ Real.sin y := by
  have hpi := Real.pi_pos
  rcases le_total y (Real.pi / 2) with h | h
  · exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (Real.mul_le_sin (by linarith) h)
  · rw [← Real.sin_pi_sub]
    exact (mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans
      (Real.mul_le_sin (by linarith) (by linarith))

lemma abs_sin_shift (N : ℕ) (y : ℝ) :
    |Real.sin (-(N : ℝ) * Real.pi - y)| = |Real.sin y| := by
  have : -(N : ℝ) * Real.pi - y = -y - N * Real.pi := by ring
  rw [this, Real.sin_sub_nat_mul_pi, Real.sin_neg]
  simp [abs_mul, abs_pow]

lemma sin_phiC_ge : 4 / 5 ≤ Real.sin phiC := by
  have hpi := Real.pi_pos
  have : phiC = Real.pi - 2 * Real.pi / 5 := by unfold phiC; ring
  rw [this, Real.sin_pi_sub]
  have := sin_lb_sym (y := 2 * Real.pi / 5) (c := 2 * Real.pi / 5) (by positivity) le_rfl
    (by linarith) (by linarith)
  have e : 2 / Real.pi * (2 * Real.pi / 5) = 4 / 5 := by field_simp; ring
  linarith

lemma cos_phiC_neg : Real.cos phiC < 0 := by
  have hpi := Real.pi_pos
  apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> unfold phiC <;> linarith

theorem EC_ray_bound_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 5 / 4 * Real.sin φ) (N0 : ℕ) {θ : ℝ} (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin φ))) := by
  have hpi := Real.pi_pos
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hφ2
  have hcφ : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hφ1 (by linarith)
  have hcosθ : Real.cos θ = Real.cos φ := by
    rcases hθ with h | h <;> simp [h]
  have habs : |(rayPt (xstar N0) θ r).im| = r * Real.sin φ := by
    rw [rayPt_im]
    have : |Real.sin θ| = Real.sin φ := by
      rcases hθ with h | h
      · rw [h]; exact abs_of_pos hsφ
      · rw [h, Real.sin_neg, abs_neg]; exact abs_of_pos hsφ
    rw [abs_mul, abs_of_nonneg hr, this]
  have key := EC_norm_le_uniform (7 / 16) (by norm_num) (rayPt (xstar N0) θ r) ?_
  · rw [habs] at key
    exact key
  · by_cases hbig : 1 / 8 ≤ |(rayPt (xstar N0) θ r).im|
    · exact Or.inl hbig
    · right
      rw [habs] at hbig
      -- δ' = -r cos θ ∈ [0, r]
      set δ := -(r * Real.cos φ) with hδ
      have hδ0 : 0 ≤ δ := by nlinarith
      have hδ1 : δ ≤ 5 / 32 := by nlinarith [mul_le_mul_of_nonneg_left hcot hr]
      have hre : Real.pi * (rayPt (xstar N0) θ r).re = -(N0 : ℝ) * Real.pi - Real.pi * (3 / 8 + δ) := by
        rw [rayPt_re, hcosθ, hδ]; unfold xstar; ring
      have hre2 : Real.pi * (rayPt (xstar N0) θ r).re - Real.pi / 4
          = -(N0 : ℝ) * Real.pi - Real.pi * (5 / 8 + δ) := by
        rw [rayPt_re, hcosθ, hδ]; unfold xstar; ring
      constructor
      · rw [hre2, abs_sin_shift]
        have := sin_lb_sym (y := Real.pi * (5 / 8 + δ)) (c := 7 * Real.pi / 32) (by positivity)
          (by nlinarith) (by nlinarith) (by linarith)
        have e : 2 / Real.pi * (7 * Real.pi / 32) = 7 / 16 := by field_simp; ring
        rw [abs_of_nonneg (by
          have : 0 ≤ Real.sin (Real.pi * (5 / 8 + δ)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith
          exact this)]
        linarith
      · rw [hre, abs_sin_shift]
        have := sin_lb_sym (y := Real.pi * (3 / 8 + δ)) (c := 3 * Real.pi / 8) (by positivity)
          (by nlinarith) (by nlinarith) (by linarith)
        have e : 2 / Real.pi * (3 * Real.pi / 8) = 3 / 4 := by field_simp; ring
        rw [abs_of_nonneg (by
          have : 0 ≤ Real.sin (Real.pi * (3 / 8 + δ)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith
          exact this)]
        linarith


/-- The integrable majorant on the rays: `‖E v_a v_b‖ ≤ C e^{-2π r sin φ} / (κ² (3/8 + r)²)`,
with `κ² = (1 - |cos φ|)/2`. -/
theorem Ev_ray_bound_gen {φ : ℝ} (hφ1 : Real.pi / 2 < φ) (hφ2 : φ < Real.pi)
    (hcot : -Real.cos φ ≤ 5 / 4 * Real.sin φ) (N0 a b : ℕ) {θ : ℝ} (hθ : θ = φ ∨ θ = -φ) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r) * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin φ)))
        * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)))) := by
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith) hφ2
  have hs : Real.sin θ ≠ 0 := by
    rcases hθ with h | h
    · rw [h]; exact ne_of_gt hsφ
    · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hsφ)
  rw [norm_mul, norm_mul]
  exact mul_le_mul (EC_ray_bound_gen hφ1 hφ2 hcot N0 hθ hr)
    (mul_le_mul (norm_inv_ray_nat_le N0 a hs hr) (norm_inv_ray_nat_le N0 b hs hr)
      (norm_nonneg _) (by have := Real.sqrt_pos.2 (kap2_pos hs); positivity))
    (by positivity) (by positivity)

lemma phiC_cot : -Real.cos phiC ≤ 5 / 4 * Real.sin phiC := by
  have := Real.neg_one_le_cos phiC
  have := Real.cos_le_one phiC
  linarith [sin_phiC_ge, Real.neg_one_le_cos phiC]

theorem EC_ray_bound (N0 : ℕ) {θ : ℝ} (hθ : θ = phiC ∨ θ = -phiC) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiC))) :=
  EC_ray_bound_gen phiC_gt phiC_lt phiC_cot N0 hθ hr

theorem Ev_ray_bound (N0 a b : ℕ) {θ : ℝ} (hθ : θ = phiC ∨ θ = -phiC) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r) * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiC)))
        * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)))) :=
  Ev_ray_bound_gen phiC_gt phiC_lt phiC_cot N0 a b hθ hr

end CatalanLambda.Decay
