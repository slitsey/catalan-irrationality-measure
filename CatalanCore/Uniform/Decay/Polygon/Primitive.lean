module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

/-!
# Segment integrals and the explicit primitive (Uniform Decay v2, Part 2, Lemma `deform`)

The segment integral `segI f a b = ∫_{[a,b]} f(z) dz` is Mathlib's curve integral of the
holomorphic 1-form `f(z) dz` along the affine segment, i.e. the paper's explicit radial
primitive `(b - a) ∫_0^1 f(a + t(b-a)) dt`.

The only analytic input is Mathlib's Poincaré lemma for convex sets: on **any** convex set `s`
(open or not) on which `f` is complex differentiable, segment integrals are additive at
corners.  Two consequences used for polygons:

* `chainI_eq` : the integral along a finite chain of segments in a convex set is the
  integral of the straight segment from the first to the last vertex (difference of primitive
  values).  Repeated vertices and self-intersections are allowed.
* `segI_split` : splitting a segment at an interior point (take `s` the segment itself).

No general Cauchy theorem is used or proved.
-/

open MeasureTheory Set

namespace CatalanCore.Uniform.Decay.Polygon

/-- The holomorphic 1-form `f(z) dz`. -/
noncomputable def form (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1 (f z)

/-- The segment integral `∫_{[a,b]} f(z) dz`. -/
noncomputable def segI (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  curveIntegral (form f) (Path.segment a b)

/-- The explicit parametrisation of a segment integral. -/
theorem segI_eq (f : ℂ → ℂ) (a b : ℂ) :
    segI f a b = ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b t) * (b - a) := by
  unfold segI
  rw [curveIntegral_segment]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp [form, mul_comm]

theorem segI_self (f : ℂ → ℂ) (a : ℂ) : segI f a a = 0 := by
  rw [segI_eq]; simp

/-- Additivity at a corner, for all three vertices in a convex set of holomorphy. -/
theorem segI_add {f : ℂ → ℂ} {s : Set ℂ}
    (hs : Convex ℝ s) (hf : DifferentiableOn ℂ f s)
    {a b c : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    segI f a b + segI f b c = segI f a c := by
  unfold segI
  apply hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
  · intro x hx
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ 1).hasFDerivAt
      |>.comp_hasDerivWithinAt x (hf x hx).hasDerivWithinAt |>.restrictScalars ℝ
  · rintro x hx u - v -
    simpa using (smul_comm u v (derivWithin f s x))
  · exact ha
  · exact hb
  · exact hc

/-- Integral along a finite chain of segments `z₀ → z₁ → ⋯ → z_k`. -/
noncomputable def chainI (f : ℂ → ℂ) : List ℂ → ℂ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => segI f a b + chainI f (b :: rest)

theorem chainI_cons_cons (f : ℂ → ℂ) (a b : ℂ) (rest : List ℂ) :
    chainI f (a :: b :: rest) = segI f a b + chainI f (b :: rest) := rfl

/-- **Primitive path independence.**  A chain in a convex set of holomorphy integrates to the
straight segment from its first to its last vertex. -/
theorem chainI_eq {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s) (hf : DifferentiableOn ℂ f s) :
    ∀ (l : List ℂ) (a : ℂ), a ∈ s → (∀ z ∈ l, z ∈ s) →
      chainI f (a :: l) = segI f a ((a :: l).getLast (List.cons_ne_nil a l))
  | [], a, _, _ => by simp [chainI, segI_self]
  | b :: rest, a, ha, hl => by
    have hb : b ∈ s := hl b (by simp)
    have hrest : ∀ z ∈ rest, z ∈ s := fun z hz => hl z (by simp [hz])
    rw [chainI_cons_cons, chainI_eq hs hf rest b hb hrest, List.getLast_cons_cons]
    have hlast : (b :: rest).getLast (List.cons_ne_nil b rest) ∈ s :=
      hl _ (List.getLast_mem _)
    exact segI_add hs hf ha hb hlast

/-- Splitting a segment at a point `e` of it.  Only differentiability along the segment is
needed (the segment itself is the convex set). -/
theorem segI_split {f : ℂ → ℂ} {a b e : ℂ} (he : e ∈ segment ℝ a b)
    (hf : ∀ z ∈ segment ℝ a b, DifferentiableAt ℂ f z) :
    segI f a e + segI f e b = segI f a b :=
  segI_add (convex_segment a b) (fun z hz => (hf z hz).differentiableWithinAt) (left_mem_segment ℝ a b)
    he (right_mem_segment ℝ a b)

/-- Norm bound for a segment integral. -/
theorem norm_segI_le {f : ℂ → ℂ} {a b : ℂ} {C : ℝ} (h : ∀ z ∈ segment ℝ a b, ‖f z‖ ≤ C) :
    ‖segI f a b‖ ≤ C * ‖b - a‖ := by
  unfold segI
  refine norm_curveIntegral_segment_le (fun z hz => ?_)
  refine (ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (h z hz)) (fun x => ?_))
  have e : form f z x = x * f z := by simp [form]
  rw [e, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (h z hz) (norm_nonneg x)

/-- A segment integral over `[p, p + T d]` is the interval integral of the affine ray
parametrisation on `[0, T]`. -/
theorem segI_ray (f : ℂ → ℂ) (p d : ℂ) {T : ℝ} (hT : 0 < T) :
    segI f p (p + (T : ℂ) * d) = ∫ u in (0 : ℝ)..T, f (p + (u : ℂ) * d) * d := by
  rw [segI_eq]
  have hl : ∀ t : ℝ, AffineMap.lineMap p (p + (T : ℂ) * d) t = p + ((T * t : ℝ) : ℂ) * d := by
    intro t
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, Complex.real_smul]
    push_cast; ring
  simp_rw [hl]
  have hmul := intervalIntegral.smul_integral_comp_mul_left
    (fun u : ℝ => f (p + (u : ℂ) * d) * d) (a := 0) (b := 1) T
  simp only [mul_zero, mul_one] at hmul
  rw [← hmul, Complex.real_smul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [add_sub_cancel_left]
  ring

end CatalanCore.Uniform.Decay.Polygon
