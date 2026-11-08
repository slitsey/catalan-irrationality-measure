module

public import CatalanMeasure.GenD.Analytic.NodalGreen
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial
noncomputable section

/-! Data-free soundness steps for the approved shared-derivative circle checker.
The numerical translation and rational parametrisation are separate obligations. -/

theorem polynomial_eval_sub_le_on_convex (p : ℂ[X]) {s : Set ℂ}
    (hs : Convex ℝ s) {M : ℝ}
    (hM : ∀ z ∈ s, ‖p.derivative.eval z‖ ≤ M) {z c : ℂ}
    (hz : z ∈ s) (hc : c ∈ s) : ‖p.eval z - p.eval c‖ ≤ M * ‖z - c‖ := by
  exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (p.hasDerivAt w).hasDerivWithinAt) hM hc hz

theorem polynomial_block_variation (p : ℂ[X]) {s : Set ℂ}
    (hs : Convex ℝ s) {M δ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ s, ‖p.derivative.eval z‖ ≤ M) {z c : ℂ}
    (hz : z ∈ s) (hc : c ∈ s) (hclose : ‖z - c‖ ≤ δ) :
    ‖p.eval z - p.eval c‖ ≤ M * δ := by
  exact (polynomial_eval_sub_le_on_convex p hs hM hz hc).trans
    (mul_le_mul_of_nonneg_left hclose hM0)

theorem ellipseH_le_of_variation {v vc : ℂ} {e H : ℝ}
    (hv : ‖v - vc‖ ≤ e) (hcenter : ellipseH vc + e ≤ H) : ellipseH v ≤ H := by
  have h := (le_abs_self (ellipseH v - ellipseH vc)).trans
    ((ellipseH_lipschitz v vc).trans hv)
  linarith

/-- The squared witness retains the sharp Bernstein ellipse growth even at H=1. -/
theorem exp_ellipseLog_le_of_square {v : ℂ} {H R : ℝ}
    (hv : ellipseH v ≤ H) (hHR : H ≤ R)
    (hsq : H ^ 2 - 1 ≤ (R - H) ^ 2) : Real.exp (ellipseLog v) ≤ R := by
  have hH : 1 ≤ H := (ellipseH_ge_one v).trans hv
  have hR : 0 ≤ R - H := sub_nonneg.mpr hHR
  have hsqrt : Real.sqrt (H ^ 2 - 1) ≤ R - H := by
    have hs := Real.sq_sqrt (by nlinarith : 0 ≤ H ^ 2 - 1)
    nlinarith [Real.sqrt_nonneg (H ^ 2 - 1)]
  have hmono : ellipseLog v ≤ Real.arcosh H := by
    exact (Real.arcosh_le_arcosh (by have := ellipseH_ge_one v; linarith)
      (by linarith)).mpr hv
  calc
    Real.exp (ellipseLog v) ≤ Real.exp (Real.arcosh H) := Real.exp_le_exp.mpr hmono
    _ = H + Real.sqrt (H ^ 2 - 1) := Real.exp_arcosh hH
    _ ≤ R := by linarith

theorem ellipseLog_le_log_of_square {v : ℂ} {H R : ℝ}
    (hv : ellipseH v ≤ H) (hHR : H ≤ R)
    (hsq : H ^ 2 - 1 ≤ (R - H) ^ 2) : ellipseLog v ≤ Real.log R := by
  have hR : 0 < R := lt_of_lt_of_le (by have := ellipseH_ge_one v; linarith) hHR
  have h := exp_ellipseLog_le_of_square hv hHR hsq
  rwa [← Real.exp_log hR, Real.exp_le_exp] at h

theorem circle_weight_le_of_power {v z : ℂ} {H R W C : ℝ}
    (hv : ellipseH v ≤ H) (hHR : H ≤ R)
    (hsq : H ^ 2 - 1 ≤ (R - H) ^ 2)
    (hz : ‖(1 : ℂ) - z‖ ≠ 0) (hW : ‖(1 : ℂ) - z‖ ^ 2 ≤ W)
    (hpower : R ^ 33 * W ^ 260 ≤ Real.exp (65 * C)) :
    (66 : ℝ) / 130 * ellipseLog v + 8 * Real.log ‖(1 : ℂ) - z‖ ≤ C := by
  have hR : 0 < R := lt_of_lt_of_le (by have := ellipseH_ge_one v; linarith) hHR
  have hn : 0 < ‖(1 : ℂ) - z‖ := (norm_nonneg _).lt_of_ne' hz
  have hWp : 0 < W := (sq_pos_of_pos hn).trans_le hW
  have hlog : 2 * Real.log ‖(1 : ℂ) - z‖ ≤ Real.log W := by
    have h := Real.log_le_log (sq_pos_of_pos hn) hW
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hp : 33 * Real.log R + 260 * Real.log W ≤ 65 * C := by
    have h := Real.log_le_log (mul_pos (pow_pos hR _) (pow_pos hWp _)) hpower
    rw [Real.log_mul (pow_pos hR _).ne' (pow_pos hWp _).ne',
      Real.log_pow, Real.log_pow, Real.log_exp] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hgreen := ellipseLog_le_log_of_square hv hHR hsq
  linarith

/-- Complete local analytic implication; the finite checker supplies each premise. -/
theorem polynomial_circle_weight_le_of_block (p : ℂ[X]) {s : Set ℂ}
    (hs : Convex ℝ s) {M δ H R W C : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ s, ‖p.derivative.eval w‖ ≤ M) {z c : ℂ}
    (hz : z ∈ s) (hc : c ∈ s) (hclose : ‖z - c‖ ≤ δ)
    (hcenter : ellipseH (p.eval c) + M * δ ≤ H) (hHR : H ≤ R)
    (hsq : H ^ 2 - 1 ≤ (R - H) ^ 2)
    (hne : ‖(1 : ℂ) - z‖ ≠ 0) (hW : ‖(1 : ℂ) - z‖ ^ 2 ≤ W)
    (hpower : R ^ 33 * W ^ 260 ≤ Real.exp (65 * C)) :
    (66 : ℝ) / 130 * ellipseLog (p.eval z) +
      8 * Real.log ‖(1 : ℂ) - z‖ ≤ C := by
  exact circle_weight_le_of_power
    (ellipseH_le_of_variation (polynomial_block_variation p hs hM0 hM hz hc hclose) hcenter)
    hHR hsq hne hW hpower

/-- The two rational branches of the upper semicircle. -/
def rationalCirclePoint (r side u : ℝ) : ℂ :=
  ⟨r * side * (1 - u ^ 2) / (1 + u ^ 2), 2 * r * u / (1 + u ^ 2)⟩

theorem rationalCirclePoint_norm_sq (r side u : ℝ) (hs : side = 1 ∨ side = -1) :
    ‖rationalCirclePoint r side u‖ ^ 2 = r ^ 2 := by
  have hd : 1 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rcases hs with rfl | rfl <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, rationalCirclePoint,
      Complex.re, Complex.im] <;> field_simp <;> ring

theorem rationalCirclePoint_chord_sq (r side u v : ℝ) (hs : side = 1 ∨ side = -1) :
    ‖rationalCirclePoint r side u - rationalCirclePoint r side v‖ ^ 2 =
      4 * r ^ 2 * (u - v) ^ 2 / ((1 + u ^ 2) * (1 + v ^ 2)) := by
  have hu : 1 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hv : 1 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rcases hs with rfl | rfl <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, rationalCirclePoint, Complex.re, Complex.im] <;>
    field_simp <;> ring

theorem rationalCirclePoint_lipschitz {r : ℝ} (hr : 0 ≤ r) (side u v : ℝ)
    (hs : side = 1 ∨ side = -1) :
    ‖rationalCirclePoint r side u - rationalCirclePoint r side v‖ ≤ 2 * r * |u - v| := by
  have hd : 0 < (1 + u ^ 2) * (1 + v ^ 2) := by positivity
  have hd1 : 1 ≤ (1 + u ^ 2) * (1 + v ^ 2) := by
    nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  have hn : 0 ≤ 4 * r ^ 2 * (u - v) ^ 2 := by positivity
  have hsq : ‖rationalCirclePoint r side u - rationalCirclePoint r side v‖ ^ 2 ≤
      4 * r ^ 2 * (u - v) ^ 2 := by
    rw [rationalCirclePoint_chord_sq r side u v hs]
    exact (div_le_iff₀ hd).mpr (by nlinarith [mul_nonneg hn (sub_nonneg.mpr hd1)])
  have ht : 0 ≤ 2 * r * |u - v| := by positivity
  have he : (2 * r * |u - v|) ^ 2 = 4 * r ^ 2 * (u - v) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  nlinarith [norm_nonneg (rationalCirclePoint r side u - rationalCirclePoint r side v)]

theorem rationalCirclePoint_mem_block {r a b u : ℝ} (hr : 0 ≤ r)
    (side : ℝ) (hs : side = 1 ∨ side = -1) (hu : u ∈ Set.Icc a b) :
    rationalCirclePoint r side u ∈
      Metric.closedBall (rationalCirclePoint r side ((a + b) / 2)) (r * (b - a)) := by
  have habs : |u - (a + b) / 2| ≤ (b - a) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    _ ≤ 2 * r * |u - (a + b) / 2| := rationalCirclePoint_lipschitz hr side _ _ hs
    _ ≤ 2 * r * ((b - a) / 2) := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = r * (b - a) := by ring

theorem filter_norm_sq_le_of_real_lower {z : ℂ} {r xmin : ℝ}
    (hz : ‖z‖ ^ 2 = r ^ 2) (hx : xmin ≤ z.re) :
    ‖(1 : ℂ) - z‖ ^ 2 ≤ 1 + r ^ 2 - 2 * xmin := by
  have hid : ‖(1 : ℂ) - z‖ ^ 2 = 1 + ‖z‖ ^ 2 - 2 * z.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [hid, hz]
  linarith

end
end CatalanMeasure.GenD.Analytic

#print axioms CatalanMeasure.GenD.Analytic.polynomial_eval_sub_le_on_convex
#print axioms CatalanMeasure.GenD.Analytic.polynomial_block_variation
#print axioms CatalanMeasure.GenD.Analytic.ellipseH_le_of_variation
#print axioms CatalanMeasure.GenD.Analytic.exp_ellipseLog_le_of_square
#print axioms CatalanMeasure.GenD.Analytic.ellipseLog_le_log_of_square
#print axioms CatalanMeasure.GenD.Analytic.circle_weight_le_of_power
#print axioms CatalanMeasure.GenD.Analytic.polynomial_circle_weight_le_of_block

#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_norm_sq

#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_chord_sq

#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_lipschitz

#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_mem_block

#print axioms CatalanMeasure.GenD.Analytic.filter_norm_sq_le_of_real_lower
