module

public import CatalanCore.Uniform.Decay.PairEnergy.Red1

@[expose] public section

/-!
# Pair energy as a boundary-energy sum, second reduction (lane D, package D6c)

Linearity of the iterated integral in the two polynomial densities (all needed integrability from
`intervalIntegrable_pot` and `segPot_continuous`).
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Tools

/-- Inner monomial potential. -/
noncomputable def Phi (A1 B1 A2 B2 : ℂ) (t0 : ℝ) (l : ℕ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t - t0) ^ l * Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖

theorem continuous_Phi (A1 B1 A2 B2 : ℂ) (hv : B2 - A2 ≠ 0) (t0 : ℝ) (l : ℕ) :
    Continuous (Phi A1 B1 A2 B2 t0 l) := by
  have hAB : A2 ≠ B2 := fun h => hv (by rw [h]; ring)
  have h1 := (segPot_continuous A2 B2 hAB (g := fun t => (t - t0) ^ l) (by fun_prop)).comp
    (show Continuous (fun s : ℝ => A1 + (s : ℂ) * (B1 - A1)) by fun_prop)
  have h2 := h1.neg
  refine h2.congr fun s => ?_
  simp only [Phi, Pi.neg_apply, Function.comp]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

theorem pair_reduce_sum (A1 B1 A2 B2 : ℂ) (hu : B1 - A1 ≠ 0) (hv : B2 - A2 ≠ 0) (s0 t0 : ℝ)
    (α β : ℕ → ℝ) (Na Nb : ℕ) :
    ∫ s in (0 : ℝ)..1, (∑ k ∈ range Na, α k * (s - s0) ^ k) *
      ∫ t in (0 : ℝ)..1, (∑ l ∈ range Nb, β l * (t - t0) ^ l) *
        (-Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
    = -∑ k ∈ range Na, ∑ l ∈ range Nb, α k * β l * Ikl A1 B1 A2 B2 s0 t0 k l := by
  -- inner integral
  have hinner : ∀ s : ℝ, ∫ t in (0 : ℝ)..1, (∑ l ∈ range Nb, β l * (t - t0) ^ l) *
        (-Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
      = -∑ l ∈ range Nb, β l * Phi A1 B1 A2 B2 t0 l s := by
    intro s
    have hint : ∀ l ∈ range Nb, IntervalIntegrable (fun t : ℝ => β l * ((t - t0) ^ l *
        Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)) volume 0 1 := by
      intro l _
      exact (intervalIntegrable_pot A2 B2 _ hv (h := fun t => (t - t0) ^ l) (by fun_prop)).const_mul (β l)
    have e : ∀ t : ℝ, (∑ l ∈ range Nb, β l * (t - t0) ^ l) *
        (-Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
        = -∑ l ∈ range Nb, β l * ((t - t0) ^ l *
          Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖) := by
      intro t; rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => by ring
    simp only [e]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_finset_sum hint]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  simp only [hinner]
  have hcont : ∀ l, Continuous (Phi A1 B1 A2 B2 t0 l) := continuous_Phi A1 B1 A2 B2 hv t0
  have hint2 : ∀ k ∈ range Na, IntervalIntegrable (fun s : ℝ => α k * (s - s0) ^ k *
      ∑ l ∈ range Nb, β l * Phi A1 B1 A2 B2 t0 l s) volume 0 1 := by
    intro k _
    refine Continuous.intervalIntegrable ?_ _ _
    have := continuous_finset_sum (range Nb) fun l _ => (continuous_const (y := β l)).mul (hcont l)
    fun_prop
  have e2 : ∀ s : ℝ, (∑ k ∈ range Na, α k * (s - s0) ^ k) * -∑ l ∈ range Nb, β l * Phi A1 B1 A2 B2 t0 l s
      = -∑ k ∈ range Na, α k * (s - s0) ^ k * ∑ l ∈ range Nb, β l * Phi A1 B1 A2 B2 t0 l s := by
    intro s; rw [mul_neg, Finset.sum_mul]
  simp only [e2]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_finset_sum hint2]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hint3 : ∀ l ∈ range Nb, IntervalIntegrable (fun s : ℝ => α k * β l * ((s - s0) ^ k *
      Phi A1 B1 A2 B2 t0 l s)) volume 0 1 := by
    intro l _
    refine Continuous.intervalIntegrable ?_ _ _
    have := hcont l
    fun_prop
  have e3 : ∀ s : ℝ, α k * (s - s0) ^ k * ∑ l ∈ range Nb, β l * Phi A1 B1 A2 B2 t0 l s
      = ∑ l ∈ range Nb, α k * β l * ((s - s0) ^ k * Phi A1 B1 A2 B2 t0 l s) := by
    intro s; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e3]
  rw [intervalIntegral.integral_finset_sum hint3]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  unfold Ikl Phi
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

end CatalanCore.Uniform.Decay.PairEnergy
