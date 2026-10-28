module

public import CatalanCore.Uniform.Decay.PairEnergy.Red3

@[expose] public section

/-!
# Pair energy: the real-variable formula (lane D, package D6c)

`pair_formula_real`: for two segments with a common point `p₁(s₀) = p₂(t₀)` and polynomial densities
`Σ α_k (s-s₀)^k`, `Σ β_l (t-t₀)^l`, the pair energy `∫ f₁ ∫ f₂ (-log ‖p₁ - p₂‖)` equals minus
four potentials of polynomial densities at the segment endpoints, minus a rational constant
(boundary energy `BE_vectors`).
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Tools
  CatalanCore.Uniform.Decay.Corners CatalanCore.Uniform.Decay.Assembly

theorem int_lin (A B z : ℂ) (hv : B - A ≠ 0) (t0 : ℝ) (c : ℕ → ℝ) (N : ℕ) :
    ∫ t in (0 : ℝ)..1, (∑ l ∈ range N, c l * (t - t0) ^ l) * Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ l ∈ range N, c l * P2 A B t0 z l := by
  have hint : ∀ l ∈ range N, IntervalIntegrable (fun t : ℝ => c l * ((t - t0) ^ l *
      Real.log ‖z - (A + (t : ℂ) * (B - A))‖)) volume 0 1 := fun l _ =>
    (intervalIntegrable_pot A B z hv (h := fun t => (t - t0) ^ l) (by fun_prop)).const_mul (c l)
  have e : ∀ t : ℝ, (∑ l ∈ range N, c l * (t - t0) ^ l) * Real.log ‖z - (A + (t : ℂ) * (B - A))‖
      = ∑ l ∈ range N, c l * ((t - t0) ^ l * Real.log ‖z - (A + (t : ℂ) * (B - A))‖) := by
    intro t; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [intervalIntegral.integral_finset_sum hint]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul]; rfl

theorem swap_sum (α β X Y : ℕ → ℝ) (Na Nb : ℕ) :
    ∑ k ∈ range Na, ∑ l ∈ range Nb, α k * β l * ((X k * Y l) / ((k : ℝ) + l + 2))
      = ∑ l ∈ range Nb, (β l * ∑ k ∈ range Na, α k * X k / ((k : ℝ) + l + 2)) * Y l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem swap_sum' (α β X Y : ℕ → ℝ) (Na Nb : ℕ) :
    ∑ k ∈ range Na, ∑ l ∈ range Nb, α k * β l * ((X k * Y l) / ((k : ℝ) + l + 2))
      = ∑ k ∈ range Na, (α k * ∑ l ∈ range Nb, β l * Y l / ((k : ℝ) + l + 2)) * X k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sq_ne_zero_of {u : ℂ} (hu : u ≠ 0) : u.re ^ 2 + u.im ^ 2 ≠ 0 := by
  have := Complex.normSq_pos.2 hu
  rw [Complex.normSq_apply] at this
  nlinarith

theorem pair_formula_real (A1 B1 A2 B2 : ℂ) (hu : B1 - A1 ≠ 0) (hv : B2 - A2 ≠ 0) (s0 t0 : ℝ)
    (hrel : A1 - A2 + (s0 : ℂ) * (B1 - A1) - (t0 : ℂ) * (B2 - A2) = 0)
    (α β : ℕ → ℝ) (Na Nb : ℕ) :
    ∫ s in (0 : ℝ)..1, (∑ k ∈ range Na, α k * (s - s0) ^ k) *
      ∫ t in (0 : ℝ)..1, (∑ l ∈ range Nb, β l * (t - t0) ^ l) *
        (-Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
    = -((∫ t in (0 : ℝ)..1, (∑ l ∈ range Nb, (β l * ∑ k ∈ range Na,
            α k * (1 - s0) ^ (k + 1) / ((k : ℝ) + l + 2)) * (t - t0) ^ l) *
          Real.log ‖(A1 + ((1 : ℝ) : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
      - (∫ t in (0 : ℝ)..1, (∑ l ∈ range Nb, (β l * ∑ k ∈ range Na,
            α k * (0 - s0) ^ (k + 1) / ((k : ℝ) + l + 2)) * (t - t0) ^ l) *
          Real.log ‖(A1 + ((0 : ℝ) : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖)
      + ((∫ s in (0 : ℝ)..1, (∑ k ∈ range Na, (α k * ∑ l ∈ range Nb,
            β l * (1 - t0) ^ (l + 1) / ((k : ℝ) + l + 2)) * (s - s0) ^ k) *
          Real.log ‖(A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) - (A1 + (s : ℂ) * (B1 - A1))‖)
      - (∫ s in (0 : ℝ)..1, (∑ k ∈ range Na, (α k * ∑ l ∈ range Nb,
            β l * (0 - t0) ^ (l + 1) / ((k : ℝ) + l + 2)) * (s - s0) ^ k) *
          Real.log ‖(A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) - (A1 + (s : ℂ) * (B1 - A1))‖))
      - ∑ k ∈ range Na, ∑ l ∈ range Nb, α k * β l / ((k : ℝ) + l + 2) *
          (((1 - s0) ^ (k + 1) - (0 - s0) ^ (k + 1)) * ((1 - t0) ^ (l + 1) - (0 - t0) ^ (l + 1))
            / (((k : ℝ) + 1) * ((l : ℝ) + 1)))) := by
  rw [pair_reduce_sum A1 B1 A2 B2 hu hv s0 t0 α β Na Nb]
  have hkl : ∀ k l : ℕ, Ikl A1 B1 A2 B2 s0 t0 k l =
      BER (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) k l
        (0 - s0) (1 - s0) (0 - t0) (1 - t0) / ((k : ℝ) + l + 2) := by
    intro k l
    have hBE := BE_vectors (ur := (B1 - A1).re) (ui := (B1 - A1).im) (vr := (B2 - A2).re)
      (vi := (B2 - A2).im) (sq_ne_zero_of hu) (sq_ne_zero_of hv)
      k l (a := 0 - s0) (b := 1 - s0) (c := 0 - t0) (d := 1 - t0) (by linarith) (by linarith)
    rw [Ikl_eq_BEL A1 B1 A2 B2 s0 t0 hrel]
    have h2 : (0 : ℝ) < (k : ℝ) + l + 2 := by positivity
    rw [eq_div_iff h2.ne']
    unfold BE at hBE
    unfold formA formB formC
    linarith
  simp only [hkl]
  have key : ∀ k l : ℕ, α k * β l * (BER (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2))
        (formC (B2 - A2)) k l (0 - s0) (1 - s0) (0 - t0) (1 - t0) / ((k : ℝ) + l + 2))
      = α k * β l * (((1 - s0) ^ (k + 1) * P2 A2 B2 t0 (A1 + ((1 : ℝ) : ℂ) * (B1 - A1)) l)
          / ((k : ℝ) + l + 2))
        - α k * β l * (((0 - s0) ^ (k + 1) * P2 A2 B2 t0 (A1 + ((0 : ℝ) : ℂ) * (B1 - A1)) l)
          / ((k : ℝ) + l + 2))
        + (α k * β l * ((P2 A1 B1 s0 (A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) k * (1 - t0) ^ (l + 1))
          / ((k : ℝ) + l + 2))
        - α k * β l * ((P2 A1 B1 s0 (A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) k * (0 - t0) ^ (l + 1))
          / ((k : ℝ) + l + 2)))
        - α k * β l / ((k : ℝ) + l + 2) *
          (((1 - s0) ^ (k + 1) - (0 - s0) ^ (k + 1)) * ((1 - t0) ^ (l + 1) - (0 - t0) ^ (l + 1))
            / (((k : ℝ) + 1) * ((l : ℝ) + 1))) := by
    intro k l
    rw [BER_eq A1 B1 A2 B2 hu hv s0 t0 hrel k l]
    ring
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [int_lin _ _ _ hv, int_lin _ _ _ hv, int_lin _ _ _ hu, int_lin _ _ _ hu]
  have h1 := swap_sum α β (fun k => (1 - s0) ^ (k + 1))
    (fun l => P2 A2 B2 t0 (A1 + ((1 : ℝ) : ℂ) * (B1 - A1)) l) Na Nb
  have h2 := swap_sum α β (fun k => (0 - s0) ^ (k + 1))
    (fun l => P2 A2 B2 t0 (A1 + ((0 : ℝ) : ℂ) * (B1 - A1)) l) Na Nb
  have h3 := swap_sum' α β (fun k => P2 A1 B1 s0 (A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) k)
    (fun l => (1 - t0) ^ (l + 1)) Na Nb
  have h4 := swap_sum' α β (fun k => P2 A1 B1 s0 (A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) k)
    (fun l => (0 - t0) ^ (l + 1)) Na Nb
  beta_reduce at h1 h2 h3 h4
  unfold P2 at h1 h2 h3 h4 ⊢
  linarith

end CatalanCore.Uniform.Decay.PairEnergy
