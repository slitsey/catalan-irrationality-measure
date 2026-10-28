module

public import CatalanCore.Uniform.Decay.Cert.Check
public import CatalanCore.Uniform.Decay.Assembly.GlobalModulus

@[expose] public section

/-!
# Semantic facts used by the concrete cell rules (lane D, package D6)

From `BasicFacts D` (the output of `basicOk_sound`): continuity, nonnegativity and the Bernstein
bound of every density, and continuity of the exact potential `U0` (from the global modulus).
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset Set CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

/-- Lower and upper Bernstein bounds of a rational polynomial density. -/
theorem ratPoly_bounds {l : List ℚ} (hne : l ≠ []) {lo hi : ℚ} (h : bernOkK l lo hi = true)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : (lo : ℝ) ≤ ratPoly l t ∧ ratPoly l t ≤ (hi : ℝ) := by
  unfold bernOkK at h
  rw [List.all_eq_true] at h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hl : ∀ k ≤ l.length - 1, lo ≤ bern (coeffs l) (l.length - 1) k ∧
      bern (coeffs l) (l.length - 1) k ≤ hi := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq, bernK_eq] at this
    exact this
  exact bernstein_range (K := ℝ) (fun i => ((coeffs l i : ℚ) : ℝ)) (l.length - 1)
    (lo := (lo : ℝ)) (hi := (hi : ℝ))
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).1)
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).2) h0 h1

variable {D : SplineData}

/-- Density facts extracted from `BasicFacts`. -/
theorem density_bounds (B : SplineData.BasicFacts D) (i : Fin D.n) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (0 : ℝ) ≤ D.f i t ∧ D.f i t ≤ (D.M i : ℝ) := by
  have := ratPoly_bounds (B.hne i) (B.hbern i) h0 h1
  unfold SplineData.f
  simpa using this

theorem density_cont (i : Fin D.n) : Continuous (D.f i) := continuous_ratPoly (D.l i)

theorem density_abs (B : SplineData.BasicFacts D) (i : Fin D.n) :
    ∀ t ∈ Icc (0 : ℝ) 1, |D.f i t| ≤ ((fun i => (D.M i : ℝ)) i) := by
  intro t ht
  have := density_bounds B i t ht.1 ht.2
  rw [abs_of_nonneg this.1]; exact this.2

theorem continuous_of_modulus {F : ℂ → ℝ} {K V : ℝ} (hK : 0 ≤ K) (hV : 0 ≤ V)
    (h : ∀ a : ℝ, 0 < a → ∀ z w, |F z - F w| ≤ K * a + V / (2 * a) * ‖z - w‖) :
    Continuous F := by
  rw [Metric.continuous_iff]
  intro b ε hε
  set a : ℝ := ε / (4 * (K + 1)) with ha
  have ha0 : 0 < a := by positivity
  have hKa : K * a < ε / 4 := by
    rw [ha, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set c : ℝ := V / (2 * a) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨ε / (2 * (c + 1)), by positivity, fun z hz => ?_⟩
  rw [Real.dist_eq]
  have h1 := h a ha0 z b
  have hd : ‖z - b‖ < ε / (2 * (c + 1)) := by rwa [dist_eq_norm] at hz
  have h2 : c * ‖z - b‖ ≤ c * (ε / (2 * (c + 1))) := mul_le_mul_of_nonneg_left hd.le hc0
  have h3 : c * (ε / (2 * (c + 1))) < ε / 2 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The exact potential `U0` of the trial measure is continuous. -/
theorem U0_continuous (B : SplineData.BasicFacts D) : Continuous (U0 D.A D.B D.f) := by
  have hf0 : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ D.f i t := fun i t ht => (density_bounds B i t ht.1 ht.2).1
  refine continuous_of_modulus (K := Real.pi * Bs D.A D.B (fun i => (D.M i : ℝ)))
    (V := Vp D.f) ?_ ?_ ?_
  · exact mul_nonneg Real.pi_pos.le
      (Finset.sum_nonneg fun i _ => div_nonneg (Rat.cast_nonneg.mpr (by
        have := density_bounds B i 0 le_rfl zero_le_one
        have h2 := (density_bounds B i 0 le_rfl zero_le_one)
        have : (0 : ℝ) ≤ (D.M i : ℝ) := h2.1.trans h2.2
        exact_mod_cast this)) (norm_nonneg _))
  · exact Finset.sum_nonneg fun i _ => intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => abs_nonneg _)
  · intro a ha z w
    have := U0_modulus B.hAB density_cont hf0 (density_abs B) ha z w
    linarith

end CatalanCore.Uniform.Decay.Cells
