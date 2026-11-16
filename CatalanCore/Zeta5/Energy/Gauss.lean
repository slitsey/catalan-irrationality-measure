module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Gaussian.lean and Apery/ZeroMass.lean (`integrable_gaussC`, `exp_gauss_le`) (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy, explicit Mathlib imports, `intervalIntegral_swap_of_continuous'` moved here from Kernel.lean. -/

/-!
# Gaussian identity and Fubini helpers for the logarithmic energy (ZD02)

* `gaussian_conv` : `∫ u : ℂ, exp (-2s‖z-u‖²) exp (-2s‖w-u‖²) = π/(4s) exp (-s‖z-w‖²)`;
* `integrable_gaussC`, `exp_gauss_le` : Gaussian domination on `ℂ`;
* `intervalIntegral_swap_of_continuous'` : Fubini for interval integrals of continuous functions.
-/

open MeasureTheory Set Real

namespace CatalanCore.Zeta5.Energy

lemma integral_gaussian_sub {b : ℝ} (c : ℝ) :
    ∫ x : ℝ, Real.exp (-b * (x - c) ^ 2) = Real.sqrt (π / b) := by
  rw [integral_sub_right_eq_self (fun x => Real.exp (-b * x ^ 2)) c]
  exact integral_gaussian b

lemma integrable_gaussian_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-b * (x - c) ^ 2)) := by
  have := (integrable_exp_neg_mul_sq hb).comp_sub_right c
  simpa using this

lemma gaussian_conv_one (s a b : ℝ) :
    ∫ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.sqrt (π / (4 * s)) * Real.exp (-s * (a - b) ^ 2) := by
  have : ∀ x : ℝ, Real.exp (-(2 * s) * (a - x) ^ 2) * Real.exp (-(2 * s) * (b - x) ^ 2) =
      Real.exp (-(4 * s) * (x - (a + b) / 2) ^ 2) * Real.exp (-s * (a - b) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [this]
  rw [integral_mul_const, integral_gaussian_sub]

/-- The norm squared on `ℂ` in terms of real and imaginary parts. -/
lemma normSq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- ZD02: the completing-the-square identity on `ℂ`. -/
lemma gaussian_conv {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ∫ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      π / (4 * s) * Real.exp (-s * ‖z - w‖ ^ 2) := by
  have h := Complex.volume_preserving_equiv_real_prod
  have key : ∀ u : ℂ, Real.exp (-(2 * s) * ‖z - u‖ ^ 2) * Real.exp (-(2 * s) * ‖w - u‖ ^ 2) =
      (Real.exp (-(2 * s) * (z.re - u.re) ^ 2) * Real.exp (-(2 * s) * (w.re - u.re) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - u.im) ^ 2) * Real.exp (-(2 * s) * (w.im - u.im) ^ 2)) := by
    intro u
    rw [normSq_eq, normSq_eq]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  simp_rw [key]
  have e := h.integral_comp' (fun p : ℝ × ℝ =>
      (Real.exp (-(2 * s) * (z.re - p.1) ^ 2) * Real.exp (-(2 * s) * (w.re - p.1) ^ 2)) *
      (Real.exp (-(2 * s) * (z.im - p.2) ^ 2) * Real.exp (-(2 * s) * (w.im - p.2) ^ 2)))
  simp only [Complex.measurableEquivRealProd_apply] at e
  rw [e, Measure.volume_eq_prod]
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-(2 * s) * (z.re - x) ^ 2) * Real.exp (-(2 * s) * (w.re - x) ^ 2))
    (fun y : ℝ => Real.exp (-(2 * s) * (z.im - y) ^ 2) * Real.exp (-(2 * s) * (w.im - y) ^ 2)),
    gaussian_conv_one s _ _, gaussian_conv_one s _ _, normSq_eq]
  simp only [Complex.sub_re, Complex.sub_im]
  rw [mul_mul_mul_comm, ← Real.sqrt_mul (by positivity), ← Real.exp_add, ← sq,
    Real.sqrt_sq (by positivity)]
  congr 2
  ring

/-- Integrability of a Gaussian on `ℂ`. -/
lemma integrable_gaussC {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) := by
  have e : (fun u : ℂ => Real.exp (-c * ‖z - u‖ ^ 2)) =
      (fun p : ℝ × ℝ => Real.exp (-c * (p.1 - z.re) ^ 2) * Real.exp (-c * (p.2 - z.im) ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext u
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply, normSq_eq,
      Complex.sub_re, Complex.sub_im, ← Real.exp_add]
    congr 1; ring
  rw [e, Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding, Measure.volume_eq_prod]
  exact (integrable_gaussian_sub hc z.re).mul_prod (integrable_gaussian_sub hc z.im)

/-- `‖γ - u‖² ≥ ‖u‖²/2 - ‖γ‖²`, in exponential form. -/
lemma exp_gauss_le {t R : ℝ} (ht : 0 ≤ t) {γ u : ℂ} (hγ : ‖γ‖ ≤ R) :
    Real.exp (-(2 * t) * ‖γ - u‖ ^ 2) ≤ Real.exp (2 * t * R ^ 2) * Real.exp (-t * ‖u‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖u‖ ≤ ‖γ - u‖ + ‖γ‖ := by
    calc ‖u‖ = ‖γ - (γ - u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖γ‖ + ‖γ - u‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have h2 : ‖u‖ ^ 2 ≤ 2 * ‖γ - u‖ ^ 2 + 2 * ‖γ‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg u) h1
    nlinarith [sq_nonneg (‖γ - u‖ - ‖γ‖)]
  have h3 : ‖γ‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg γ]
  nlinarith

/-- Fubini for interval integrals of a continuous function of two variables. -/
lemma intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  refine IntegrableOn.mono_set ?_ (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hf.continuousOn

/-- Fubini for interval integrals of continuous functions, arbitrary orientation. -/
lemma intervalIntegral_swap_of_continuous' {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f))
    (a b c d : ℝ) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · exact intervalIntegral_swap_of_continuous hf hab hcd
  · rw [intervalIntegral.integral_symm d c]
    simp_rw [intervalIntegral.integral_symm d c, intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [intervalIntegral.integral_symm b a]
    simp_rw [intervalIntegral.integral_symm b a]
    rw [intervalIntegral.integral_neg, intervalIntegral_swap_of_continuous hf hab hcd]
  · rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm d c]
    simp_rw [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm d c,
      intervalIntegral.integral_neg]
    rw [intervalIntegral_swap_of_continuous hf hab hcd]

end CatalanCore.Zeta5.Energy
