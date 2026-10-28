module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
@[expose] public section

/-!
# Closed forms for logarithmic potentials and energies of interval densities

For the real logarithm (`Real.log s = log |s|`, `log 0 = 0`):

* `Lam s = s log|s| - s` has `Lam' = log|s|`;
* `Hfun s = (1/2) s² log|s| - (3/4) s²` has `Hfun' = Lam`;
* the potential of density `w` on `[lo, hi]` at a real point `x` is
  `-w (Lam (x - lo) - Lam (x - hi))` (log and linear terms only);
* the mutual energy of `[a,b]` and `[c,d]` (unit densities) is
  `Hfun (b-d) + Hfun (a-c) - Hfun (b-c) - Hfun (a-d)`.

All hold for arbitrary real endpoints, including overlapping intervals and singular
diagonals; the iterated-integral forms are exact.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Real intervalIntegral

noncomputable def Lam (s : ℝ) : ℝ := s * Real.log s - s

noncomputable def Hfun (s : ℝ) : ℝ := s ^ 2 * Real.log s / 2 - 3 / 4 * s ^ 2

theorem continuous_Lam : Continuous Lam :=
  Real.continuous_mul_log.sub continuous_id

theorem continuous_Hfun : Continuous Hfun := by
  have : Hfun = fun s => s * (s * Real.log s) / 2 - 3 / 4 * s ^ 2 := by
    funext s; unfold Hfun; ring
  rw [this]
  exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).sub
    (continuous_const.mul (continuous_pow 2))

theorem hasDerivAt_Lam {s : ℝ} (hs : s ≠ 0) : HasDerivAt Lam (Real.log s) s := by
  have h := ((hasDerivAt_id s).mul (Real.hasDerivAt_log hs)).sub (hasDerivAt_id s)
  refine h.congr_deriv ?_
  simp [hs]

theorem hasDerivAt_Hfun {s : ℝ} (hs : s ≠ 0) : HasDerivAt Hfun (Lam s) s := by
  have h := (((hasDerivAt_pow 2 s).mul (Real.hasDerivAt_log hs)).div_const 2).sub
    ((hasDerivAt_pow 2 s).const_mul (3 / 4))
  refine h.congr_deriv ?_
  unfold Lam
  field_simp
  ring

/-- FTC for a continuous function whose antiderivative is differentiable off `0`. -/
theorem integral_eq_sub_off_zero {F f : ℝ → ℝ} (hF : Continuous F) (hf : Continuous f)
    (hd : ∀ x, x ≠ 0 → HasDerivAt F (f x) x) (p q : ℝ) :
    ∫ x in p..q, f x = F q - F p := by
  have aux : ∀ a b : ℝ, a ≤ b → 0 ∉ Set.Ioo a b → ∫ x in a..b, f x = F b - F a := by
    intro a b hab h0
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF.continuousOn
      (fun x hx => hd x (fun h => h0 (h ▸ hx))) (hf.intervalIntegrable _ _)
  have main : ∀ a b : ℝ, a ≤ b → ∫ x in a..b, f x = F b - F a := by
    intro a b hab
    by_cases h0 : 0 ∈ Set.Ioo a b
    · rw [← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable a 0) (hf.intervalIntegrable 0 b)]
      rw [aux a 0 h0.1.le (fun h => lt_irrefl _ h.2), aux 0 b h0.2.le (fun h => lt_irrefl _ h.1)]
      ring
    · exact aux a b hab h0
  rcases le_total p q with h | h
  · exact main p q h
  · rw [intervalIntegral.integral_symm, main q p h]; ring

theorem integral_log_eq_Lam (p q : ℝ) : ∫ s in p..q, Real.log s = Lam q - Lam p := by
  rw [integral_log]; unfold Lam; ring

theorem integral_Lam_eq_Hfun (p q : ℝ) : ∫ s in p..q, Lam s = Hfun q - Hfun p :=
  integral_eq_sub_off_zero continuous_Hfun continuous_Lam (fun _ hx => hasDerivAt_Hfun hx) p q

theorem Hfun_neg (s : ℝ) : Hfun (-s) = Hfun s := by
  unfold Hfun; rw [Real.log_neg_eq_log]; ring

/-- Potential (without the weight) of the unit density on `[lo, hi]` at a real point. -/
theorem integral_neg_log_abs (x lo hi : ℝ) :
    ∫ t in lo..hi, -Real.log |x - t| = -(Lam (x - lo) - Lam (x - hi)) := by
  have h1 : ∀ t : ℝ, -Real.log |x - t| = -Real.log (x - t) := fun t => by rw [Real.log_abs]
  simp_rw [h1]
  rw [intervalIntegral.integral_neg]
  have := intervalIntegral.integral_comp_sub_left (a := lo) (b := hi) (fun s => Real.log s) x
  rw [this, integral_log_eq_Lam]

/-- Exact mutual energy of two unit-density intervals (iterated integral). -/
noncomputable def pairEnergy (a b c d : ℝ) : ℝ :=
  Hfun (b - d) + Hfun (a - c) - Hfun (b - c) - Hfun (a - d)

theorem pairEnergy_eq_integral (a b c d : ℝ) :
    ∫ x in a..b, ∫ t in c..d, -Real.log |x - t| = pairEnergy a b c d := by
  have h1 : ∀ x : ℝ, ∫ t in c..d, -Real.log |x - t| = -(Lam (x - c) - Lam (x - d)) :=
    fun x => integral_neg_log_abs x c d
  simp_rw [h1]
  have hc : ∀ e : ℝ, ∫ x in a..b, Lam (x - e) = Hfun (b - e) - Hfun (a - e) := by
    intro e
    exact (intervalIntegral.integral_comp_sub_right Lam e).trans (integral_Lam_eq_Hfun _ _)
  have hi : ∀ e : ℝ, IntervalIntegrable (fun x => Lam (x - e)) MeasureTheory.volume a b :=
    fun e => (continuous_Lam.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_sub (hi c) (hi d), hc, hc]
  unfold pairEnergy
  ring

theorem pairEnergy_comm (a b c d : ℝ) : pairEnergy a b c d = pairEnergy c d a b := by
  unfold pairEnergy
  rw [← Hfun_neg (b - d), ← Hfun_neg (a - c), ← Hfun_neg (b - c), ← Hfun_neg (a - d)]
  simp only [neg_sub]
  ring

end CatalanCore.Uniform.Decay.Nodes
