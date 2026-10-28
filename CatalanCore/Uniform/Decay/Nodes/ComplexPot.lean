module
public import CatalanCore.Uniform.Decay.Nodes.Scaled
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
@[expose] public section

/-!
# Closed-form potential of an interval density at a non-real point

For `z = x + i y`, `y ≠ 0`, and the piece `w` on `[lo, hi]`:

`w ∫_{lo}^{hi} elog z t dt = -(w/2) (Gy y (x - lo) - Gy y (x - hi))`,
`Gy y s = s log (s² + y²) - 2 s + 2 y arctan (s / y)` (log, linear and arctan terms),
`(Gy y)' = log (s² + y²)`.  (`Regular.Gk` is the case `y = 1`.)  For real points see
`Closed.integral_neg_log_abs`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open MeasureTheory intervalIntegral

noncomputable def Gy (y s : ℝ) : ℝ := s * Real.log (s ^ 2 + y ^ 2) - 2 * s + 2 * y * Real.arctan (s / y)

theorem hasDerivAt_Gy {y : ℝ} (hy : y ≠ 0) (s : ℝ) :
    HasDerivAt (Gy y) (Real.log (s ^ 2 + y ^ 2)) s := by
  have hpos : (s ^ 2 + y ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2) (2 * s) s := by
    have := (hasDerivAt_pow 2 s).add_const (y ^ 2)
    simpa using this
  have h2 := h1.log hpos
  have h3 := ((hasDerivAt_id s).mul h2).sub ((hasDerivAt_id s).const_mul 2)
  have h5 : HasDerivAt (fun s : ℝ => s / y) (1 / y) s := by
    simpa using (hasDerivAt_id s).div_const y
  have h6 := (h5.arctan).const_mul (2 * y)
  have h4 := h3.add h6
  refine h4.congr_deriv ?_
  simp only [id]
  have hy2 : (0 : ℝ) < y ^ 2 := by positivity
  field_simp
  ring

theorem continuous_Gy {y : ℝ} (hy : y ≠ 0) : Continuous (Gy y) :=
  continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_Gy hy s).continuousAt)

/-- Interval potential at a non-real point: log, linear and arctan terms only. -/
theorem integral_elog_complex (z : ℂ) (hy : z.im ≠ 0) (lo hi : ℝ) :
    ∫ t in lo..hi, CatalanLambda.Decay.elog z (t : ℂ) =
      -(1 / 2) * (Gy z.im (z.re - lo) - Gy z.im (z.re - hi)) := by
  have h1 : ∀ t : ℝ, CatalanLambda.Decay.elog z (t : ℂ) =
      (fun s : ℝ => -(1 / 2) * Real.log (s ^ 2 + z.im ^ 2)) (z.re - t) := by
    intro t
    rw [← kern_eq_elog]; unfold kern; congr 2
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => -(1 / 2) * Real.log (s ^ 2 + z.im ^ 2)) z.re,
    intervalIntegral.integral_const_mul]
  have : ∫ s in (z.re - hi)..(z.re - lo), Real.log (s ^ 2 + z.im ^ 2) =
      Gy z.im (z.re - lo) - Gy z.im (z.re - hi) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_Gy hy s) ?_
    have hpos : 0 < z.im ^ 2 := by positivity
    exact (Continuous.log (by fun_prop) (fun s => by positivity)).intervalIntegrable _ _
  rw [this]

/-- The potential of a piece at a non-real point, in closed form. -/
theorem Piece_potC_closed (P : Piece) (z : ℂ) (hy : z.im ≠ 0) :
    P.w * ∫ t in P.lo..P.hi, CatalanLambda.Decay.elog z (t : ℂ) =
      -(P.w / 2) * (Gy z.im (z.re - P.lo) - Gy z.im (z.re - P.hi)) := by
  rw [integral_elog_complex z hy]; ring

end CatalanCore.Uniform.Decay.Nodes
