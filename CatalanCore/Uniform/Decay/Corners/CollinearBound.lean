module

public import CatalanCore.Uniform.Decay.Corners.Quadrant

@[expose] public section

/-!
# Collinear case `B² = A C`: domination estimates

For `A, C > 0`, `B² = A C` the form is a square, `qf A B C s t = A (s + κ t)²` with `κ = B/A ≠ 0`
(the two supporting lines coincide: `u, v` are real multiples of one another), so `L = ½ log qf`
is singular along the whole line `s + κ t = 0`.  This module proves the estimates needed to pass
to the limit `δ → 0⁺` in the identity for the positive definite forms `(A+δ, B, C+δ)`:

* `qf_collinear`, `kappa_ne_zero`;
* `Lq_reg_bound`: `|L'| ≤ c + |log (s + κ t)|` whenever `A (s+κt)² ≤ qf' ≤ K' R`;
* `abslog_affine_integrable`: `|log (α + κ x)|` is interval integrable (`κ ≠ 0`);
* `abslog_shear_integrableOn`: `|log (s + κ t)|` is integrable on every bounded rectangle
  (shear `(t,s) ↦ (t, s + κ t)` is measure preserving).
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C : ℝ}

theorem qf_collinear (hA : 0 < A) (hB : B ^ 2 = A * C) (s t : ℝ) :
    qf A B C s t = A * (s + B / A * t) ^ 2 := by
  have hC : C = B ^ 2 / A := by field_simp; linarith
  rw [hC]; unfold qf; field_simp; ring

theorem kappa_ne_zero (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) : B / A ≠ 0 := by
  have : B ≠ 0 := by
    intro h0; rw [h0] at hB; nlinarith [mul_pos hA hC]
  exact div_ne_zero this hA.ne'

theorem Lq_reg_bound (hA : 0 < A) {κ A' C' K' R s t : ℝ} (hw : s + κ * t ≠ 0)
    (hlow : A * (s + κ * t) ^ 2 ≤ qf A' B C' s t) (hup : qf A' B C' s t ≤ K' * R) :
    |Lq A' B C' s t| ≤ (|Real.log A| + |Real.log (K' * R)|) / 2 + |Real.log (s + κ * t)| := by
  have hp : 0 < A * (s + κ * t) ^ 2 := by positivity
  have hb := abs_log_le_of_bounds hp hlow hup
  have hlp : Real.log (A * (s + κ * t) ^ 2) = Real.log A + 2 * Real.log (s + κ * t) := by
    rw [Real.log_mul hA.ne' (by positivity), Real.log_pow]; push_cast; ring
  rw [hlp] at hb
  have e1 := abs_add_le (Real.log A) (2 * Real.log (s + κ * t))
  rw [abs_mul, abs_two] at e1
  unfold Lq
  rw [abs_div, abs_two]
  linarith

theorem abslog_affine_integrable (α : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (p q : ℝ) :
    IntervalIntegrable (fun x : ℝ => |Real.log (α + κ * x)|) volume p q := by
  have h0 : IntervalIntegrable (fun x : ℝ => |Real.log x|) volume (κ * p + α) (κ * q + α) :=
    (intervalIntegral.intervalIntegrable_log').abs
  have h1 := h0.comp_add_right α
  have h2 := h1.comp_mul_left (c := κ)
  simp only [add_sub_cancel_right, mul_div_cancel_left₀ _ hκ] at h2
  simpa [add_comm] using h2

theorem abslog_shear_integrableOn (κ : ℝ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntegrableOn (fun p : ℝ × ℝ => |Real.log (p.1 + κ * p.2)|) (Ioc a b ×ˢ Ioc c d) := by
  set M : ℝ := |κ| * max |c| |d| with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  set G : ℝ × ℝ → ℝ := fun q => |Real.log q.2| with hG
  set box : Set (ℝ × ℝ) := Ioc c d ×ˢ Ioc (a - M) (b + M) with hbox
  have hboxm : MeasurableSet box := measurableSet_Ioc.prod measurableSet_Ioc
  have hlogI : IntegrableOn (fun u : ℝ => |Real.log u|) (Ioc (a - M) (b + M)) := by
    have := (intervalIntegral.intervalIntegrable_log' (a := a - M) (b := b + M)).abs
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 this
  have hprod : Integrable (fun z : ℝ × ℝ => (fun _ : ℝ => (1 : ℝ)) z.1 * |Real.log z.2|)
      ((volume.restrict (Ioc c d)).prod (volume.restrict (Ioc (a - M) (b + M)))) :=
    Integrable.mul_prod (integrable_const 1) hlogI
  rw [Measure.prod_restrict] at hprod
  have hGbox : IntegrableOn G box (volume.prod volume) := by
    simpa [hG, hbox, IntegrableOn] using hprod
  have hGind : Integrable (box.indicator G) (volume.prod volume) :=
    (integrable_indicator_iff hboxm).2 hGbox
  have hPmp : MeasurePreserving (fun q : ℝ × ℝ => (q.1, q.2 + κ * q.1))
      (volume.prod volume) (volume.prod volume) := by
    have := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
      (g := fun t s => s + κ * t) (by unfold Function.uncurry; fun_prop)
      (Filter.Eventually.of_forall fun t => map_add_right_eq_self (volume : Measure ℝ) (κ * t))
    exact this
  have hcomp := hPmp.integrable_comp_of_integrable hGind
  have hset : IntegrableOn (fun q : ℝ × ℝ => |Real.log (q.2 + κ * q.1)|)
      (Ioc c d ×ˢ Ioc a b) (volume.prod volume) := by
    refine hcomp.integrableOn.congr_fun (fun q hq => ?_)
      (measurableSet_Ioc.prod measurableSet_Ioc)
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hq
    have hq1 : |q.1| ≤ max |c| |d| := abs_le.2
      ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, le_abs_self (-c)],
       by linarith [le_abs_self d, le_max_right |c| |d|]⟩
    have hk : |κ * q.1| ≤ M := by rw [abs_mul, hM]; exact mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)
    have hk' := abs_le.1 hk
    have hmem : (q.1, q.2 + κ * q.1) ∈ box := ⟨⟨h1, h2⟩, ⟨by linarith, by linarith⟩⟩
    simp only [Function.comp, Set.indicator_of_mem hmem, hG]
  rw [Measure.volume_eq_prod]
  exact hset.swap

end CatalanCore.Uniform.Decay.Corners
