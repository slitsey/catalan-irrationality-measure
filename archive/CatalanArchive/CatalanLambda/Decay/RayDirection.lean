module

public import CatalanLambda.Decay.RayBound

@[expose] public section

/-!
# The rational ray direction `(-1, 3)`

`phiR = π - arctan 3` is the angle of the direction `(-1, 3)`.  Instances of the general
contour identity and ray bounds for this angle.
-/

open Complex MeasureTheory Set

namespace CatalanLambda.Decay

/-- The angle of the direction `(-1, 3)`: `π - arctan 3`. -/
noncomputable def phiR : ℝ := Real.pi - Real.arctan 3

lemma phiR_gt : Real.pi / 2 < phiR := by
  unfold phiR
  have := Real.arctan_lt_pi_div_two 3
  linarith

lemma phiR_lt : phiR < Real.pi := by
  unfold phiR
  have := Real.arctan_pos.2 (show (0 : ℝ) < 3 by norm_num)
  linarith

lemma sin_phiR : Real.sin phiR = 3 / Real.sqrt 10 := by
  unfold phiR
  rw [Real.sin_pi_sub, Real.sin_arctan]
  norm_num

lemma cos_phiR : Real.cos phiR = -(1 / Real.sqrt 10) := by
  unfold phiR
  rw [Real.cos_pi_sub, Real.cos_arctan]
  norm_num

lemma phiR_cot : -Real.cos phiR ≤ 5 / 4 * Real.sin phiR := by
  rw [sin_phiR, cos_phiR]
  have : 0 < Real.sqrt 10 := by positivity
  rw [neg_neg]
  have h : 1 / Real.sqrt 10 ≤ 5 / 4 * (3 / Real.sqrt 10) := by
    rw [← sub_nonneg]
    have : 5 / 4 * (3 / Real.sqrt 10) - 1 / Real.sqrt 10 = (11 / 4) / Real.sqrt 10 := by ring
    rw [this]; positivity
  exact h

theorem contour_identity_R (N0 a b : ℕ) :
    ((16 * Tent a b : ℝ) : ℂ)
      = -((∑ m ∈ Finset.range N0, atomTerm a b m : ℝ) : ℂ)
        + (2 * Real.pi * I)⁻¹ *
          contL (xstar N0) phiR (fun z => EC z * ((z - a)⁻¹ * (z - b)⁻¹)) :=
  contour_identity_gen phiR_gt phiR_lt N0 a b

theorem EC_ray_bound_R (N0 : ℕ) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiR))) :=
  EC_ray_bound_gen phiR_gt phiR_lt phiR_cot N0 hθ hr

theorem Ev_ray_bound_R (N0 a b : ℕ) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ} (hr : 0 ≤ r) :
    ‖EC (rayPt (xstar N0) θ r) * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)‖
      ≤ (16 * Real.pi + Real.pi * Real.exp (Real.pi / 4) / (7 / 16) ^ 2)
        * Real.exp (-(2 * Real.pi * (r * Real.sin phiR)))
        * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)) * (1 / (Real.sqrt (kap2 θ) * (3 / 8 + r)))) :=
  Ev_ray_bound_gen phiR_gt phiR_lt phiR_cot N0 a b hθ hr

theorem integrableOn_E_ray_R (N0 a b : ℕ) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR) :
    IntegrableOn (fun r : ℝ => (EC (rayPt (xstar N0) θ r)
      * ((rayPt (xstar N0) θ r - a)⁻¹ * (rayPt (xstar N0) θ r - b)⁻¹)) * exp ((θ : ℂ) * I))
      (Ioi 0) := by
  have hs : 0 < Real.sin phiR := by rw [sin_phiR]; positivity
  apply integrableOn_E_ray
  rcases hθ with h | h
  · rw [h]; exact ne_of_gt hs
  · rw [h, Real.sin_neg]; exact neg_ne_zero.2 (ne_of_gt hs)

end CatalanLambda.Decay
