import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Phase 0: explicit segment-integral primitive and a real interior chi3 corner.
The primitive is the line integral from a fixed base point, precisely the
paper's radial integral. Mathlib's convex primitive theorem supplies its derivative.
This file does not claim the real initial endpoint or the improper tail bridge.
-/
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

open scoped Topology
open MeasureTheory Set

namespace CatalanCore.Uniform.Decay.PilotCorner

noncomputable def form (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1 (f z)

noncomputable def primitive (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  curveIntegral (form f) (Path.segment a z)

/-- This is the paper's explicit radial primitive, with a real affine parameter. -/
theorem primitive_eq_radial (f : ℂ → ℂ) (a z : ℂ) :
    primitive f a z = (z - a) *
      ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a z t) := by
  unfold primitive
  rw [curveIntegral_segment]
  change (∫ t in (0 : ℝ)..1, (z - a) * f (AffineMap.lineMap a z t)) = _
  rw [intervalIntegral.integral_const_mul]

/-- The explicit radial segment integral has derivative f on any convex domain. -/
theorem primitive_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ}
    (hs : Convex ℝ s) (hf : DifferentiableOn ℂ f s)
    {a z : ℂ} (ha : a ∈ s) (hz : z ∈ s) :
    HasDerivWithinAt (primitive f a) (f z) s z := by
  apply hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
  · intro x hx
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).hasFDerivAt
      |>.comp_hasDerivWithinAt x (hf x hx).hasDerivWithinAt |>.restrictScalars ℝ
  · rintro x hx u - v -
    simpa using (smul_comm u v (derivWithin f s x))
  · exact ha
  · exact hz

/-- Finite corner removal, with all three vertices in the holomorphy domain. -/
theorem corner_add {f : ℂ → ℂ} {s : Set ℂ}
    (hs : Convex ℝ s) (hf : DifferentiableOn ℂ f s)
    {a b c : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    curveIntegral (form f) (Path.segment a b) +
      curveIntegral (form f) (Path.segment b c) = primitive f a c := by
  apply hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
  · intro x hx
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).hasFDerivAt
      |>.comp_hasDerivWithinAt x (hf x hx).hasDerivWithinAt |>.restrictScalars ℝ
  · rintro x hx u - v -
    simpa using (smul_comm u v (derivWithin f s x))
  · exact ha
  · exact hb
  · exact hc

def upper : Set ℂ := {z | 0 < z.im}

noncomputable def shiftedCot (s : ℝ) (z : ℂ) : ℂ :=
  Complex.cos ((Real.pi : ℂ) * (z + s)) /
    Complex.sin ((Real.pi : ℂ) * (z + s))

theorem shifted_sin_ne_zero (s : ℝ) {z : ℂ} (hz : z ∈ upper) :
    Complex.sin ((Real.pi : ℂ) * (z + s)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hi := congrArg Complex.im hk
  have hzero : Real.pi * z.im = 0 := by simpa [Complex.mul_im] using hi
  exact (mul_ne_zero Real.pi_ne_zero (ne_of_gt hz)) hzero

theorem shiftedCot_differentiableAt (s : ℝ) {z : ℂ} (hz : z ∈ upper) :
    DifferentiableAt ℂ (shiftedCot s) z := by
  have harg : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) * (w + s)) z := by
    fun_prop
  exact ((Complex.differentiable_cos.differentiableAt.comp z harg).div
    (Complex.differentiable_sin.differentiableAt.comp z harg)
    (shifted_sin_ne_zero s hz))

/-- Actual chi3 source integrand E(z)/((z-a)(z-b)), including diagonal a=b. -/
noncomputable def chi3Source (a b : ℕ) (z : ℂ) : ℂ :=
  -(Real.pi : ℂ) * ((1 / 18 : ℂ) * shiftedCot (1 / 3) z -
    (1 / 12 : ℂ) * shiftedCot (1 / 2) z + (1 / 36 : ℂ) * shiftedCot 1 z) /
    ((z - a) * (z - b))

theorem chi3Source_differentiableOn (a b : ℕ) :
    DifferentiableOn ℂ (chi3Source a b) upper := by
  intro z hz
  have h1 := shiftedCot_differentiableAt (1 / 3) hz
  have h2 := shiftedCot_differentiableAt (1 / 2) hz
  have h3 := shiftedCot_differentiableAt 1 hz
  have hn (n : ℕ) : z - (n : ℂ) ≠ 0 := by
    intro heq
    have hi := congrArg Complex.im (sub_eq_zero.mp heq)
    have : z.im = 0 := by simpa using hi
    exact (ne_of_gt hz) this
  have hden : DifferentiableAt ℂ (fun w : ℂ => (w - a) * (w - b)) z := by
    fun_prop
  exact ((((h1.const_mul (1 / 18 : ℂ)).sub (h2.const_mul (1 / 12 : ℂ))).add
    (h3.const_mul (1 / 36 : ℂ))).const_mul (-(Real.pi : ℂ)) |>.div
    hden (mul_ne_zero (hn a) (hn b))).differentiableWithinAt

-- Exact rational reconstruction from the selected chi3 decimal heights and leans.
noncomputable def p1 : ℂ := ⟨-0.1 + (-0.5341500350645203) * 0.042495133047399575,
  0.042495133047399575⟩
noncomputable def p2 : ℂ := ⟨p1.re + (-0.4721222614562869) *
  (0.1274853991421987 - p1.im), 0.1274853991421987⟩
noncomputable def p3 : ℂ := ⟨p2.re + (-0.36277948981216984) *
  (0.23372323176069765 - p2.im), 0.23372323176069765⟩

/-- One actual selected chi3 interior corner, with arbitrary integer row/column nodes. -/
theorem chi3_corner (a b : ℕ) :
    curveIntegral (form (chi3Source a b)) (Path.segment p1 p2) +
      curveIntegral (form (chi3Source a b)) (Path.segment p2 p3) =
      primitive (chi3Source a b) p1 p3 := by
  apply corner_add (convex_halfSpace_im_gt 0) (chi3Source_differentiableOn a b)
  all_goals norm_num [upper, p1, p2, p3]

#print axioms primitive_hasDerivWithinAt
#print axioms chi3_corner

end CatalanCore.Uniform.Decay.PilotCorner
