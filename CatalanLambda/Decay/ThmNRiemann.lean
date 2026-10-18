module

public import CatalanLambda.Decay.ThmNNodes
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

/-!
# Theorem N_ρ, stage 3c: [R1], Riemann sum against `U^τ` for points left of the origin
-/

open Finset MeasureTheory intervalIntegral

namespace CatalanLambda.Decay

lemma norm_sub_real_sq (σ : ℂ) (u : ℝ) : ‖σ - (u : ℂ)‖ ^ 2 = (σ.re - u) ^ 2 + σ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

lemma norm_sub_real_pos {σ : ℂ} (hσ : σ.re < 0) {u : ℝ} (hu : 0 ≤ u) : 0 < ‖σ - (u : ℂ)‖ := by
  apply norm_pos_iff.2
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma logNorm_mono {σ : ℂ} (hσ : σ.re < 0) :
    MonotoneOn (fun u : ℝ => Real.log ‖σ - (u : ℂ)‖) (Set.Ici 0) := by
  intro u hu u' hu' huu'
  simp only [Set.mem_Ici] at hu hu'
  apply Real.log_le_log (norm_sub_real_pos hσ hu)
  have h1 : ‖σ - (u : ℂ)‖ ^ 2 ≤ ‖σ - (u' : ℂ)‖ ^ 2 := by
    rw [norm_sub_real_sq, norm_sub_real_sq]
    nlinarith [sq_nonneg σ.im]
  exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _) |>.trans le_rfl

/-- **[R1]**: the left Riemann sum against `U^τ`. -/
theorem riemann_node_sum {h : ℕ} (hh : 0 < h) {σ : ℂ} (hσ : σ.re < 0) :
    ∑ b ∈ range h, elog σ (nodeC h b) ≤ h * Utau σ + Real.log (1 + 1 / ‖σ‖) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  set f : ℝ → ℝ := fun u => Real.log ‖σ - (u : ℂ)‖ with hf
  set g : ℝ → ℝ := fun x => f (x / h) with hg
  have hgm : MonotoneOn g (Set.Icc 0 (0 + (h : ℝ))) := by
    intro x hx y hy hxy
    apply logNorm_mono hσ
    · exact div_nonneg hx.1 hh'.le
    · exact div_nonneg hy.1 hh'.le
    · exact div_le_div_of_nonneg_right hxy hh'.le
  have h1 := hgm.integral_le_sum
  have hint : ∫ x in (0 : ℝ)..0 + h, g x = h * ∫ u in (0 : ℝ)..1, f u := by
    rw [zero_add, hg]
    simp only
    rw [intervalIntegral.integral_comp_div (fun u => f u) hh'.ne']
    simp [smul_eq_mul]
    left; rw [div_self hh'.ne']
  rw [hint] at h1
  have hsum : ∑ i ∈ range h, g (0 + ((i + 1 : ℕ) : ℝ))
      = ∑ b ∈ range h, f (b / h) + (f 1 - f 0) := by
    have e1 : ∀ i ∈ range h, g (0 + ((i + 1 : ℕ) : ℝ)) = f (((i + 1 : ℕ) : ℝ) / h) := by
      intro i _; simp [hg]
    rw [Finset.sum_congr rfl e1]
    have := Finset.sum_range_succ (fun i : ℕ => f ((i : ℝ) / h)) h
    have h2 := Finset.sum_range_succ' (fun i : ℕ => f ((i : ℝ) / h)) h
    have h3 : f ((h : ℝ) / h) = f 1 := by rw [div_self hh'.ne']
    have h4 : f (((0 : ℕ) : ℝ) / h) = f 0 := by simp
    rw [h3] at this
    rw [h4] at h2
    linarith
  rw [hsum] at h1
  have hU : Utau σ = -∫ u in (0 : ℝ)..1, f u := by
    unfold Utau; rw [intervalIntegral.integral_neg]
  have hfd : f 1 - f 0 ≤ Real.log (1 + 1 / ‖σ‖) := by
    have hp0 : 0 < ‖σ - ((0 : ℝ) : ℂ)‖ := norm_sub_real_pos hσ le_rfl
    have hp1 : 0 < ‖σ - ((1 : ℝ) : ℂ)‖ := norm_sub_real_pos hσ zero_le_one
    simp only [hf]
    rw [← Real.log_div hp1.ne' hp0.ne']
    apply Real.log_le_log (div_pos hp1 hp0)
    have hσn : 0 < ‖σ‖ := by simpa using hp0
    simp only [Complex.ofReal_zero, sub_zero]
    rw [div_le_iff₀ hσn]
    have : ‖σ - ((1 : ℝ) : ℂ)‖ ≤ ‖σ‖ + 1 := by
      have := norm_sub_le σ ((1 : ℝ) : ℂ)
      simpa using this
    have e : (1 + 1 / ‖σ‖) * ‖σ‖ = ‖σ‖ + 1 := by field_simp
    linarith
  have hsumE : ∑ b ∈ range h, elog σ (nodeC h b) = -∑ b ∈ range h, f (b / h) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [elog, nodeC, hf]
  rw [hsumE, hU]
  nlinarith [h1, hfd]

end CatalanLambda.Decay
