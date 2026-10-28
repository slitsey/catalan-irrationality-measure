module

public import CatalanCore.Uniform.Decay.Tools.BernsteinList
public import CatalanCore.Uniform.Decay.Spline.Errors

@[expose] public section

/-!
# Rational polynomial densities: Bernstein `|f| ≤ M` and the presentation bounds (lane D, D2)

A signed segment-polynomial trial piece has density `ratPoly l` (rational coefficient list `l`).
The Bernstein checker `bernOkK l (-M) M` (for both `f` and `-f`) gives `|f| ≤ M` on `[0,1]`, hence

* `Vp f ≤ ∑ M_i` (presentation total-variation bound), and
* the arclength-density sum `Bs A B M = ∑ M_i / L_i`.

No polynomial root isolation is needed.
-/

namespace CatalanCore.Uniform.Decay.Spline

open CatalanCore.Uniform.Decay.Tools Finset intervalIntegral

variable {n : ℕ}

/-- The real polynomial with rational coefficient list `l`. -/
noncomputable def ratPoly (l : List ℚ) (t : ℝ) : ℝ :=
  ∑ i ∈ range (l.length - 1 + 1), ((coeffs l i : ℚ) : ℝ) * t ^ i

theorem continuous_ratPoly (l : List ℚ) : Continuous (ratPoly l) := by
  unfold ratPoly
  fun_prop

theorem bern_cast (a : ℕ → ℚ) (d k : ℕ) :
    bern (fun i => ((a i : ℚ) : ℝ)) d k = ((bern a d k : ℚ) : ℝ) := by
  unfold bern
  push_cast
  rfl

/-- **Bernstein bound for a rational polynomial density.** -/
theorem ratPoly_abs_le {l : List ℚ} (hne : l ≠ []) {M : ℚ} (h : bernOkK l (-M) M = true)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : |ratPoly l t| ≤ (M : ℝ) := by
  unfold bernOkK at h
  rw [List.all_eq_true] at h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hl : ∀ k ≤ l.length - 1, -M ≤ bern (coeffs l) (l.length - 1) k ∧
      bern (coeffs l) (l.length - 1) k ≤ M := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq, bernK_eq] at this
    exact this
  have := bernstein_range (K := ℝ) (fun i => ((coeffs l i : ℚ) : ℝ)) (l.length - 1)
    (lo := -(M : ℝ)) (hi := (M : ℝ))
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).1)
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).2) h0 h1
  rw [abs_le]
  exact this

/-- `∫₀¹ |f| ≤ M` when `|f| ≤ M` on `[0,1]`. -/
theorem integral_abs_le {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ M) : ∫ t in (0 : ℝ)..1, |f t| ≤ M := by
  have h1 : IntervalIntegrable (fun t => |f t|) MeasureTheory.volume 0 1 :=
    hf.abs.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 0 1 := intervalIntegrable_const
  have := intervalIntegral.integral_mono_on (zero_le_one' ℝ) h1 h2 hM
  simpa using this

/-- Presentation total variation from the pointwise bounds. -/
theorem Vp_le_sum {f : Fin n → ℝ → ℝ} (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) : Vp f ≤ ∑ i, M i :=
  Finset.sum_le_sum (fun i _ => integral_abs_le (hf i) (hM i))

end CatalanCore.Uniform.Decay.Spline
