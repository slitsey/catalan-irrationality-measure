module
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import CatalanCore.Uniform.Decay.Nodes.Count
@[expose] public section

/-!
# Stieltjes (Abel) discrepancy for node sums

`abel_discrepancy` is Lemma `IBP` of Uniform Decay v2 Part 1: if the counting function of a node
list is within `D` of a continuous limiting CDF `Λ` on `[0, b]`, then for every `C¹` kernel `g`
the node sum differs from the Stieltjes integral `g(b) Λ(b) - ∫ g' Λ` by at most
`D (|g b| + ∫ |g'|)`.  `piece_ibp` identifies the Stieltjes integral of a block piece
with `w ∫_{lo}^{hi} g`.
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset MeasureTheory Set intervalIntegral

/-- Indicator coefficients of a finite node set. -/
def indic (A : Finset ℕ) (k : ℕ) : ℝ := if k ∈ A then 1 else 0

/-- The counting function `N(t) = #{j ∈ A, j ≤ t}`, as an Abel partial sum. -/
theorem sum_indic_Icc (A : Finset ℕ) (n : ℕ) :
    ∑ k ∈ Icc 0 n, indic A k = ((A.filter (fun j : ℕ => j ≤ n)).card : ℝ) := by
  unfold indic
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext j
  simp [Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem sum_mul_indic (A : Finset ℕ) (g : ℝ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 0 n, g k * indic A k = ∑ j ∈ A.filter (fun j : ℕ => j ≤ n), g j := by
  unfold indic
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- **Abel discrepancy.** -/
theorem abel_discrepancy (c : ℕ → ℝ) {g g' Λ : ℝ → ℝ} {b D : ℝ} (hb : 0 ≤ b)
    (hg : ∀ t ∈ Icc 0 b, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc 0 b))
    (hΛ : Continuous Λ)
    (hD : ∀ t ∈ Icc 0 b, |∑ k ∈ Icc 0 ⌊t⌋₊, c k - Λ t| ≤ D) :
    |∑ k ∈ Icc 0 ⌊b⌋₊, g k * c k - (g b * Λ b - ∫ t in Ioc 0 b, g' t * Λ t)| ≤
      D * (|g b| + ∫ t in Ioc 0 b, |g' t|) := by
  have hdiff : ∀ t ∈ Icc 0 b, DifferentiableAt ℝ g t := fun t ht => (hg t ht).differentiableAt
  have hder : ∀ t ∈ Icc 0 b, deriv g t = g' t := fun t ht => (hg t ht).deriv
  have hg'int : IntegrableOn g' (Icc 0 b) := hg'.integrableOn_Icc
  have hint : IntegrableOn (deriv g) (Icc 0 b) :=
    hg'int.congr_fun (fun t ht => (hder t ht).symm) measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul c hb hdiff hint
  set N : ℝ → ℝ := fun t => ∑ k ∈ Icc 0 ⌊t⌋₊, c k with hN
  have hNint : IntegrableOn (fun t => deriv g t * N t) (Icc 0 b) :=
    integrableOn_mul_sum_Icc (a := 0) (b := b) (m := 0) c le_rfl hint
  have hNint' : IntegrableOn (fun t => g' t * N t) (Ioc 0 b) := by
    refine (hNint.mono_set Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [hder t (Ioc_subset_Icc_self ht)]
  have hΛint : IntegrableOn (fun t => g' t * Λ t) (Ioc 0 b) := by
    refine (ContinuousOn.integrableOn_Icc (hg'.mul hΛ.continuousOn)).mono_set
      Ioc_subset_Icc_self
  have hEq : ∑ k ∈ Icc 0 ⌊b⌋₊, g k * c k - (g b * Λ b - ∫ t in Ioc 0 b, g' t * Λ t) =
      g b * (N b - Λ b) - ∫ t in Ioc 0 b, g' t * (N t - Λ t) := by
    rw [hab]
    have : ∫ t in Ioc 0 b, deriv g t * N t = ∫ t in Ioc 0 b, g' t * N t := by
      refine setIntegral_congr_fun measurableSet_Ioc ?_
      intro t ht
      simp only [hder t (Ioc_subset_Icc_self ht)]
    rw [this]
    simp_rw [mul_sub]
    rw [integral_sub hNint' hΛint]
    simp only [hN]
    ring
  rw [hEq]
  have hbN : |N b - Λ b| ≤ D := hD b ⟨hb, le_rfl⟩
  have hint2 : ‖∫ t in Ioc 0 b, g' t * (N t - Λ t)‖ ≤ ∫ t in Ioc 0 b, |g' t| * D := by
    refine norm_integral_le_of_norm_le ?_ ?_
    · exact (hg'int.mono_set Ioc_subset_Icc_self).abs.mul_const D
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro t ht
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hD t (Ioc_subset_Icc_self ht)) (abs_nonneg _)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hbN
  have : ∫ t in Ioc 0 b, |g' t| * D = D * ∫ t in Ioc 0 b, |g' t| := by
    rw [MeasureTheory.integral_mul_const]; ring
  calc |g b * (N b - Λ b) - ∫ t in Ioc 0 b, g' t * (N t - Λ t)|
      ≤ |g b * (N b - Λ b)| + |∫ t in Ioc 0 b, g' t * (N t - Λ t)| := abs_sub _ _
    _ ≤ |g b| * D + D * ∫ t in Ioc 0 b, |g' t| := by
        refine add_le_add ?_ (by rw [← this]; simpa [Real.norm_eq_abs] using hint2)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hbN (abs_nonneg _)
    _ = D * (|g b| + ∫ t in Ioc 0 b, |g' t|) := by ring

end CatalanCore.Uniform.Decay.Nodes
