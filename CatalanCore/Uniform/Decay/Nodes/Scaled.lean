module
public import CatalanCore.Uniform.Decay.Nodes.Discrepancy
@[expose] public section

/-!
# Scaled free-point potential discrepancy for block geometries (Part 1, Lemma `free-potential`)

For `σ = z/r` at distance `≥ δ/r` from `[0, B]` the counting potential
`∑_{j∈R_r} elog (z/r) (j/r)` of the row list differs from `r · U_{μ_R}(z/r)` by at most
`D (|kern z b| + 2 (log M - log δ)) + K log r` with explicit
`D = rowConstR` and `K = rowConst` (the mass-rounding constant).  `U_μ` is the scaled
potential `ppotC` of the limiting row measure `rowPieces`.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

namespace Decay.Nodes

/-- Potential at a complex point of a node measure: `∑_P w_P ∫_{lo}^{hi} elog σ t dt`. -/
noncomputable def ppotC (ps : List Piece) (σ : ℂ) : ℝ :=
  (ps.map fun P => P.w * ∫ t in P.lo..P.hi, elog σ (t : ℂ)).sum

theorem intervalIntegrable_kern (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (kern z) MeasureTheory.volume a b := by
  by_cases him : z.im = 0
  · have h : kern z = fun t => -(Real.log (z.re - t)) := by
      funext t
      unfold kern
      rw [him, zero_pow two_ne_zero, add_zero, Real.log_pow]
      push_cast; ring
    rw [h]
    have := (intervalIntegral.intervalIntegrable_log' (a := z.re - a) (b := z.re - b)).comp_sub_left z.re
    simp only [sub_sub_cancel] at this
    exact this.neg
  · have hpos : 0 < z.im ^ 2 := by positivity
    have : Continuous (kern z) := by
      unfold kern
      refine continuous_const.mul (Continuous.log (by fun_prop) (fun t => ?_))
      positivity
    exact this.intervalIntegrable _ _

theorem intervalIntegrable_elog (σ : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => elog σ (t : ℂ)) MeasureTheory.volume a b := by
  have : (fun t : ℝ => elog σ (t : ℂ)) = kern σ := by
    funext t; exact (kern_eq_elog σ t).symm
  rw [this]; exact intervalIntegrable_kern σ a b

theorem elog_scale_real (z : ℂ) (r : ℝ) (hr : 0 < r) (t : ℝ) (hne : z / r ≠ (t : ℂ)) :
    elog z ((r * t : ℝ) : ℂ) = elog (z / r) (t : ℂ) - Real.log r := by
  unfold elog
  have : z - ((r * t : ℝ) : ℂ) = (r : ℂ) * (z / r - (t : ℂ)) := by
    push_cast
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hn : ‖z / r - (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.log_mul hr.ne' hn]; ring

/-- Unscaled piece integral versus scaled piece integral. -/
theorem piece_integral_scale (z : ℂ) {r : ℕ} (hr : 0 < r) (w u v : ℝ) :
    w * ∫ x in (u * r)..(v * r), elog z (x : ℂ) =
      r * (w * ∫ t in u..v, elog (z / r) (t : ℂ)) - r * (w * (v - u)) * Real.log r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h1 : ∫ x in (u * r)..(v * r), elog z (x : ℂ) =
      r * ∫ t in u..v, elog z ((r * t : ℝ) : ℂ) := by
    have := intervalIntegral.integral_comp_mul_left (a := u) (b := v)
      (fun x : ℝ => elog z (x : ℂ)) hr'.ne'
    rw [mul_comm u, mul_comm v]
    rw [this]
    simp only [smul_eq_mul]
    field_simp
  have hae : ∀ᵐ t : ℝ, z / r ≠ (t : ℂ) := by
    have h0 : ∀ᵐ t : ℝ, t ∉ ({(z / r).re} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem MeasureTheory.volume
    filter_upwards [h0] with t ht heq
    apply ht
    have := congrArg Complex.re heq
    simp only [Complex.ofReal_re] at this
    simp [this]
  have h2 : ∫ t in u..v, elog z ((r * t : ℝ) : ℂ) =
      (∫ t in u..v, elog (z / r) (t : ℂ)) - (v - u) * Real.log r := by
    have h3 : ∫ t in u..v, elog z ((r * t : ℝ) : ℂ) =
        ∫ t in u..v, (elog (z / r) (t : ℂ) - Real.log r) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with t ht _
      exact elog_scale_real z r hr' t ht
    rw [h3, intervalIntegral.integral_sub (intervalIntegrable_elog (z / r) u v)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [h1, h2]
  ring

end Decay.Nodes
end CatalanCore.Uniform
