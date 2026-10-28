module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
@[expose] public section

/-!
# Closed-form logarithmic potential of a polynomial density on a segment

For a segment `A + t (B - A)`, `t ∈ [0,1]`, and a polynomial density `∑ a_k t^k`, the potential
`∫₀¹ p(t) log‖z - (A + t(B-A))‖ dt` is, with `ζ = (z - A)/(B - A)`,
`∑ a_k ( log‖B-A‖/(k+1) + Re (Gk k ζ 1 - Gk k ζ 0) )`
where `Gk k ζ s = ((s^(k+1) - ζ^(k+1))/(k+1)) Log(s - ζ) - (1/(k+1)) ∑_{j≤k} ζ^(k-j) s^(j+1)/(j+1)`.
Only logarithms and arguments appear (through `Re`/`Im` of `Log`): there is no dilogarithm.
The key point is `d/ds Gk = s^k Log(s - ζ)` (`hasDerivAt_Gk`).
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset Complex intervalIntegral

/-- Elementary antiderivative of `s ↦ s^k L s`, where `L' = 1/(s - ζ)` (`L` is a branch of
`Log (s - ζ)`). -/
noncomputable def GkL (k : ℕ) (ζ : ℂ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((s ^ (k + 1) - ζ ^ (k + 1)) / ((k : ℂ) + 1)) * L s
    - (1 / ((k : ℂ) + 1)) * ∑ j ∈ range (k + 1), ζ ^ (k - j) * s ^ (j + 1) / ((j : ℂ) + 1)

theorem hasDerivAt_GkL (k : ℕ) (ζ s : ℂ) (L : ℂ → ℂ) (hne : s - ζ ≠ 0)
    (h2 : HasDerivAt L (1 / (s - ζ)) s) :
    HasDerivAt (GkL k ζ L) (s ^ k * L s) s := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : HasDerivAt (fun s : ℂ => (s ^ (k + 1) - ζ ^ (k + 1)) / ((k : ℂ) + 1))
      (s ^ k) s := by
    have := ((hasDerivAt_pow (k + 1) s).sub_const (ζ ^ (k + 1))).div_const ((k : ℂ) + 1)
    convert this using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have h3 : HasDerivAt (fun s : ℂ => ∑ j ∈ range (k + 1), ζ ^ (k - j) * s ^ (j + 1) / ((j : ℂ) + 1))
      (∑ j ∈ range (k + 1), ζ ^ (k - j) * s ^ j) s := by
    have := HasDerivAt.fun_sum (u := range (k + 1))
      (A := fun j s => ζ ^ (k - j) * s ^ (j + 1) / ((j : ℂ) + 1))
      (A' := fun j => ζ ^ (k - j) * s ^ j) (x := s) (fun j _ => by
        have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have := (((hasDerivAt_pow (j + 1) s).const_mul (ζ ^ (k - j))).div_const ((j : ℂ) + 1))
        convert this using 1
        simp only [Nat.add_sub_cancel]
        push_cast
        field_simp)
    exact this
  have key := (h1.mul h2).sub (h3.const_mul (1 / ((k : ℂ) + 1)))
  unfold GkL
  convert key using 1
  -- algebra: geometric sum identity
  have hgeom : (∑ j ∈ range (k + 1), s ^ j * ζ ^ (k + 1 - 1 - j)) * (s - ζ) = s ^ (k + 1) - ζ ^ (k + 1) :=
    geom_sum₂_mul s ζ (k + 1)
  have hsum : ∑ j ∈ range (k + 1), ζ ^ (k - j) * s ^ j = (s ^ (k + 1) - ζ ^ (k + 1)) / (s - ζ) := by
    rw [eq_div_iff hne, ← hgeom]
    simp only [Nat.add_sub_cancel]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  field_simp
  ring

/-- Branch `Log (s - ζ)`. -/
noncomputable def Gk (k : ℕ) (ζ s : ℂ) : ℂ := GkL k ζ (fun s => Complex.log (s - ζ)) s

/-- Branch `Log (ζ - s)` (same real part on the real line: `log ‖s - ζ‖`). -/
noncomputable def Gk' (k : ℕ) (ζ s : ℂ) : ℂ := GkL k ζ (fun s => Complex.log (ζ - s)) s

theorem hasDerivAt_Gk (k : ℕ) (ζ s : ℂ) (hs : s - ζ ∈ slitPlane) :
    HasDerivAt (Gk k ζ) (s ^ k * Complex.log (s - ζ)) s :=
  hasDerivAt_GkL k ζ s _ (slitPlane_ne_zero hs) (((hasDerivAt_id s).sub_const ζ).clog hs)

theorem hasDerivAt_Gk' (k : ℕ) (ζ s : ℂ) (hs : ζ - s ∈ slitPlane) :
    HasDerivAt (Gk' k ζ) (s ^ k * Complex.log (ζ - s)) s := by
  have hne : s - ζ ≠ 0 := by
    intro h; exact slitPlane_ne_zero hs (by rw [← neg_sub, h, neg_zero])
  refine hasDerivAt_GkL k ζ s _ hne ?_
  have := ((hasDerivAt_id s).const_sub ζ).clog hs
  simp only [id] at this
  convert this using 1
  have h2 : ζ - s ≠ 0 := slitPlane_ne_zero hs
  rw [← neg_sub, one_div, neg_div, ← one_div, neg_div']
  field_simp

/-- Real-variable derivative of the real part, at `t` where `t - ζ` is in the slit plane. -/
theorem hasDerivAt_Gk_re (k : ℕ) (ζ : ℂ) (t : ℝ) (ht : (t : ℂ) - ζ ∈ slitPlane) :
    HasDerivAt (fun x : ℝ => (Gk k ζ (x : ℂ)).re) (t ^ k * Real.log ‖(t : ℂ) - ζ‖) t := by
  have h := (hasDerivAt_Gk k ζ (t : ℂ) ht).real_of_complex
  have e : (((t : ℂ) ^ k * Complex.log ((t : ℂ) - ζ))).re
      = t ^ k * Real.log ‖(t : ℂ) - ζ‖ := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.log_re]
  rw [e] at h
  exact h

theorem hasDerivAt_Gk'_re (k : ℕ) (ζ : ℂ) (t : ℝ) (ht : ζ - (t : ℂ) ∈ slitPlane) :
    HasDerivAt (fun x : ℝ => (Gk' k ζ (x : ℂ)).re) (t ^ k * Real.log ‖(t : ℂ) - ζ‖) t := by
  have h := (hasDerivAt_Gk' k ζ (t : ℂ) ht).real_of_complex
  have e : (((t : ℂ) ^ k * Complex.log (ζ - (t : ℂ)))).re
      = t ^ k * Real.log ‖(t : ℂ) - ζ‖ := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.log_re, ← norm_neg, neg_sub]
  rw [e] at h
  exact h

private theorem cont_pow_mul_log (k : ℕ) (ζ : ℂ) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, (t : ℂ) - ζ ≠ 0) :
    ContinuousOn (fun t : ℝ => t ^ k * Real.log ‖(t : ℂ) - ζ‖) (Set.Icc 0 1) := by
  refine (continuousOn_pow k).mul (ContinuousOn.log ?_ ?_)
  · exact (Complex.continuous_ofReal.sub continuous_const).norm.continuousOn
  · intro t ht
    exact norm_ne_zero_iff.mpr (h t ht)

/-- **Moment potential, branch 1**: if `t - ζ` avoids `(-∞, 0]` for `t ∈ [0,1]`. -/
theorem integral_pow_mul_log_norm (k : ℕ) (ζ : ℂ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, (t : ℂ) - ζ ∈ slitPlane) :
    ∫ t in (0 : ℝ)..1, t ^ k * Real.log ‖(t : ℂ) - ζ‖ = (Gk k ζ 1 - Gk k ζ 0).re := by
  have hc := cont_pow_mul_log k ζ (fun t ht => slitPlane_ne_zero (h t ht))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (Gk k ζ (x : ℂ)).re) (f' := fun t => t ^ k * Real.log ‖(t : ℂ) - ζ‖)
    (a := 0) (b := 1)
    (fun x hx => hasDerivAt_Gk_re k ζ x (h x (by simpa [Set.uIcc_of_le zero_le_one] using hx)))
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa using this

/-- **Moment potential, branch 2**: if `ζ - t` avoids `(-∞, 0]` for `t ∈ [0,1]`
(e.g. `ζ` real and `ζ > 1`, or `ζ` non-real). -/
theorem integral_pow_mul_log_norm' (k : ℕ) (ζ : ℂ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ζ - (t : ℂ) ∈ slitPlane) :
    ∫ t in (0 : ℝ)..1, t ^ k * Real.log ‖(t : ℂ) - ζ‖ = (Gk' k ζ 1 - Gk' k ζ 0).re := by
  have hc := cont_pow_mul_log k ζ (fun t ht hz => slitPlane_ne_zero (h t ht)
    (by rw [← neg_sub, hz, neg_zero]))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (Gk' k ζ (x : ℂ)).re) (f' := fun t => t ^ k * Real.log ‖(t : ℂ) - ζ‖)
    (a := 0) (b := 1)
    (fun x hx => hasDerivAt_Gk'_re k ζ x (h x (by simpa [Set.uIcc_of_le zero_le_one] using hx)))
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa using this

/-- Pointwise factorisation of the segment distance. -/
theorem log_norm_segment (A B z : ℂ) (hAB : B - A ≠ 0) (t : ℝ)
    (ht : (t : ℂ) - (z - A) / (B - A) ≠ 0) :
    Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = Real.log ‖B - A‖ + Real.log ‖(t : ℂ) - (z - A) / (B - A)‖ := by
  have e : z - (A + (t : ℂ) * (B - A)) = -((B - A) * ((t : ℂ) - (z - A) / (B - A))) := by
    field_simp
    ring
  rw [e, norm_neg, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hAB) (norm_ne_zero_iff.mpr ht)]

/-- **Closed-form potential of a polynomial density on a segment** (no dilogarithm):
`∫₀¹ (∑ a_k t^k) log‖z - (A + t(B-A))‖ dt
  = ∑ a_k (log‖B-A‖/(k+1) + Re (Gk k ζ 1 - Gk k ζ 0))`, `ζ = (z-A)/(B-A)`,
provided `t - ζ` avoids the branch cut `(-∞,0]` for `t ∈ [0,1]` (all `z` off the
half-line `A + [0,∞)(B-A)`... i.e. whenever `ζ ∉ [0,∞)`). -/
theorem segment_potential (a : ℕ → ℝ) (d : ℕ) (A B z : ℂ) (hAB : B - A ≠ 0)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, (t : ℂ) - (z - A) / (B - A) ∈ slitPlane) :
    ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), a k * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ k ∈ range (d + 1), a k * (Real.log ‖B - A‖ / ((k : ℝ) + 1) +
          (Gk k ((z - A) / (B - A)) 1 - Gk k ((z - A) / (B - A)) 0).re) := by
  set ζ : ℂ := (z - A) / (B - A) with hζ
  set L : ℝ := Real.log ‖B - A‖ with hL
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, (t : ℂ) - ζ ≠ 0 := fun t ht => slitPlane_ne_zero (h t ht)
  have hcongr : ∫ t in (0 : ℝ)..1, (∑ k ∈ range (d + 1), a k * t ^ k) *
        Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∫ t in (0 : ℝ)..1, ∑ k ∈ range (d + 1),
          a k * (L * t ^ k + t ^ k * Real.log ‖(t : ℂ) - ζ‖) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using ht

    rw [log_norm_segment A B z hAB t (hne t ht'), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hc := cont_pow_mul_log k ζ hne
    have hi1 : IntervalIntegrable (fun t : ℝ => L * t ^ k) MeasureTheory.volume 0 1 :=
      (continuousOn_const.mul (continuousOn_pow k)).intervalIntegrable_of_Icc zero_le_one
    have hi2 : IntervalIntegrable (fun t : ℝ => t ^ k * Real.log ‖(t : ℂ) - ζ‖)
        MeasureTheory.volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow_mul_log_norm k ζ h]
    congr 1
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    push_cast
    ring
  · intro k _
    have hc := cont_pow_mul_log k ζ hne
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    exact continuousOn_const.mul ((continuousOn_const.mul (continuousOn_pow k)).add hc)

end CatalanCore.Uniform.Decay.Tools
