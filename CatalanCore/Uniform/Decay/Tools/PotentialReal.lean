module
public import CatalanCore.Uniform.Decay.Tools.Potential
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
@[expose] public section

/-!
# Segment potential when the field point is on the support line (real `ζ`)

For real `r = ζ` (field point `z = A + r (B-A)`, anywhere on the support line, including the
segment itself) the moment integral `∫₀¹ t^k log|t - r| dt = Hk 1 - Hk 0` holds for every real `r`,
with the real antiderivative `Hk k r t = ((t^(k+1) - r^(k+1))/(k+1)) log|t-r| - (1/(k+1)) ∑ ...`.
Together with `segment_potential` (non-real `ζ`, or real `ζ<0`) this covers all field points.
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset intervalIntegral

/-- Real antiderivative of `t^k log |t - r|`. -/
noncomputable def Hk (k : ℕ) (r t : ℝ) : ℝ :=
  ((t ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1)) * Real.log (t - r)
    - (1 / ((k : ℝ) + 1)) * ∑ j ∈ range (k + 1), r ^ (k - j) * t ^ (j + 1) / ((j : ℝ) + 1)

theorem hasDerivAt_Hk (k : ℕ) (r t : ℝ) (ht : t ≠ r) :
    HasDerivAt (Hk k r) (t ^ k * Real.log (t - r)) t := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hne : t - r ≠ 0 := sub_ne_zero.2 ht
  have h1 : HasDerivAt (fun s : ℝ => (s ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1)) (t ^ k) t := by
    have := ((hasDerivAt_pow (k + 1) t).sub_const (r ^ (k + 1))).div_const ((k : ℝ) + 1)
    convert this using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have h2 : HasDerivAt (fun s : ℝ => Real.log (s - r)) (1 / (t - r)) t := by
    have := ((hasDerivAt_id t).sub_const r).log hne
    simpa using this
  have h3 : HasDerivAt (fun s : ℝ => ∑ j ∈ range (k + 1), r ^ (k - j) * s ^ (j + 1) / ((j : ℝ) + 1))
      (∑ j ∈ range (k + 1), r ^ (k - j) * t ^ j) t := by
    have := HasDerivAt.fun_sum (u := range (k + 1))
      (A := fun j s => r ^ (k - j) * s ^ (j + 1) / ((j : ℝ) + 1))
      (A' := fun j => r ^ (k - j) * t ^ j) (x := t) (fun j _ => by
        have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
        have := (((hasDerivAt_pow (j + 1) t).const_mul (r ^ (k - j))).div_const ((j : ℝ) + 1))
        convert this using 1
        simp only [Nat.add_sub_cancel]
        push_cast
        field_simp)
    exact this
  have key := (h1.mul h2).sub (h3.const_mul (1 / ((k : ℝ) + 1)))
  unfold Hk
  convert key using 1
  have hgeom : (∑ j ∈ range (k + 1), t ^ j * r ^ (k + 1 - 1 - j)) * (t - r)
      = t ^ (k + 1) - r ^ (k + 1) := geom_sum₂_mul t r (k + 1)
  have hsum : ∑ j ∈ range (k + 1), r ^ (k - j) * t ^ j = (t ^ (k + 1) - r ^ (k + 1)) / (t - r) := by
    rw [eq_div_iff hne, ← hgeom]
    simp only [Nat.add_sub_cancel]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  field_simp
  ring

theorem continuous_Hk (k : ℕ) (r : ℝ) : Continuous (Hk k r) := by
  unfold Hk
  have hq : ∀ t : ℝ, (t ^ (k + 1) - r ^ (k + 1)) = (t - r) *
      ∑ j ∈ range (k + 1), t ^ j * r ^ (k + 1 - 1 - j) := fun t =>
    (geom_sum₂_mul t r (k + 1)).symm.trans (mul_comm _ _)
  have hc : Continuous fun t : ℝ => (t - r) * Real.log (t - r) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have hform : (fun t : ℝ => ((t ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1)) * Real.log (t - r))
      = fun t => ((∑ j ∈ range (k + 1), t ^ j * r ^ (k + 1 - 1 - j)) / ((k : ℝ) + 1)) *
          ((t - r) * Real.log (t - r)) := by
    ext t; rw [hq t]; ring
  have : Continuous fun t : ℝ => ((t ^ (k + 1) - r ^ (k + 1)) / ((k : ℝ) + 1)) *
      Real.log (t - r) := by
    rw [hform]; fun_prop
  exact this.sub (by fun_prop)

theorem intervalIntegrable_pow_log (k : ℕ) (r a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => t ^ k * Real.log (t - r)) MeasureTheory.volume a b := by
  have h1 : IntervalIntegrable (fun t : ℝ => Real.log (t - r)) MeasureTheory.volume a b := by
    have := (intervalIntegral.intervalIntegrable_log' (a := a - r) (b := b - r)).comp_sub_right r
    simpa using this
  exact h1.continuousOn_mul (g := fun t : ℝ => t ^ k) (continuousOn_pow k)

/-- Moment integral on an interval whose interior misses the singular point. -/
theorem integral_pow_mul_log_real_of_le (k : ℕ) (r a b : ℝ) (hab : a ≤ b)
    (hr : r ∉ Set.Ioo a b) :
    ∫ t in a..b, t ^ k * Real.log (t - r) = Hk k r b - Hk k r a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (continuous_Hk k r).continuousOn
    (fun x hx => hasDerivAt_Hk k r x (fun h => hr (h ▸ hx)))
    (intervalIntegrable_pow_log k r a b)

/-- **Moment potential for every real `r`** (field point anywhere on the support line). -/
theorem integral_pow_mul_log_real (k : ℕ) (r : ℝ) :
    ∫ t in (0 : ℝ)..1, t ^ k * Real.log (t - r) = Hk k r 1 - Hk k r 0 := by
  set m : ℝ := min 1 (max 0 r) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (le_max_left _ _)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmv : (r ≤ 0 → m = 0) ∧ (0 ≤ r → r ≤ 1 → m = r) ∧ (1 ≤ r → m = 1) := by
    refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
    · rw [hm, max_eq_left h]; exact min_eq_right zero_le_one
    · rw [hm, max_eq_right h]; exact min_eq_right h'
    · rw [hm, max_eq_right (by linarith)]; exact min_eq_left h
  have h1 : r ∉ Set.Ioo (0 : ℝ) m := by
    intro ⟨h, h'⟩
    rcases le_total r 1 with h3 | h3
    · have := hmv.2.1 h.le h3; linarith
    · have := hmv.2.2 h3; linarith
  have h2 : r ∉ Set.Ioo m 1 := by
    intro ⟨h, h'⟩
    rcases le_total r 0 with h3 | h3
    · have := hmv.1 h3; linarith
    · have := hmv.2.1 h3 h'.le; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_pow_log k r 0 m) (intervalIntegrable_pow_log k r m 1),
    integral_pow_mul_log_real_of_le k r 0 m hm0 h1, integral_pow_mul_log_real_of_le k r m 1 hm1 h2]
  ring

/-- **Segment potential, field point on the support line** (`z = A + r (B-A)`, any real `r`;
includes points on the segment itself). -/
theorem segment_potential_real (a : ℕ → ℝ) (d : ℕ) (A B z : ℂ) (r : ℝ) (hAB : B - A ≠ 0)
    (hz : (z - A) / (B - A) = (r : ℂ)) :
    ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), a k * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ k ∈ range (d + 1), a k * (Real.log ‖B - A‖ / ((k : ℝ) + 1) +
          (Hk k r 1 - Hk k r 0)) := by
  set L : ℝ := Real.log ‖B - A‖ with hL
  have hzz : z - A = r * (B - A) := by
    rw [div_eq_iff hAB] at hz; exact hz
  have hcongr : ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), a k * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∫ t in (0 : ℝ)..1, ∑ k ∈ range (d + 1),
          a k * (L * t ^ k + t ^ k * Real.log (t - r)) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ∉ ({r} : Set ℝ) :=
      (Set.countable_singleton r).ae_notMem _
    filter_upwards [hae] with t ht _
    have htr : t - r ≠ 0 := sub_ne_zero.2 (by simpa using ht)
    have e : z - (A + (t : ℂ) * (B - A)) = -((B - A) * ((t - r : ℝ) : ℂ)) := by
      have : z = A + r * (B - A) := by linear_combination hzz
      rw [this]; push_cast; ring
    have hn : ((t - r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htr
    rw [e, norm_neg, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hAB) (norm_ne_zero_iff.mpr hn),
      Complex.norm_real, Real.norm_eq_abs, Real.log_abs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hi1 : IntervalIntegrable (fun t : ℝ => L * t ^ k) MeasureTheory.volume 0 1 :=
      (continuousOn_const.mul (continuousOn_pow k)).intervalIntegrable_of_Icc zero_le_one
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hi1 (intervalIntegrable_pow_log k r 0 1),
      intervalIntegral.integral_const_mul, integral_pow, integral_pow_mul_log_real k r]
    congr 1
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    push_cast
    ring
  · intro k _
    have hi1 : IntervalIntegrable (fun t : ℝ => L * t ^ k) MeasureTheory.volume 0 1 :=
      (continuousOn_const.mul (continuousOn_pow k)).intervalIntegrable_of_Icc zero_le_one
    exact (hi1.add (intervalIntegrable_pow_log k r 0 1)).const_mul (a k)

/-- Non-real `ζ`: the branch hypothesis of `segment_potential` holds automatically. -/
theorem segment_potential_nonreal (a : ℕ → ℝ) (d : ℕ) (A B z : ℂ) (hAB : B - A ≠ 0)
    (him : ((z - A) / (B - A)).im ≠ 0) :
    ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), a k * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ k ∈ range (d + 1), a k * (Real.log ‖B - A‖ / ((k : ℝ) + 1) +
          (Gk k ((z - A) / (B - A)) 1 - Gk k ((z - A) / (B - A)) 0).re) :=
  segment_potential a d A B z hAB fun t _ => Or.inr (by simpa using him)

end CatalanCore.Uniform.Decay.Tools
