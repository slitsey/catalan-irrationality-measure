module

public import CatalanCore.Uniform.Decay.PairEnergy.Red2

@[expose] public section

/-!
# Pair energy as a boundary-energy sum, third reduction (lane D, package D6c)

`BER` of the pair, rewritten through the monomial potentials of the two segments at the four
segment endpoints (`P2 z l = ∫₀¹ (t-t₀)^l log ‖z - p₂(t)‖`, `P1 z k = ∫₀¹ (s-s₀)^k log ‖z - p₁(s)‖`).
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Tools
  CatalanCore.Uniform.Decay.Corners CatalanCore.Uniform.Decay.Assembly

/-- Monomial potential of segment 2. -/
noncomputable def P2 (A2 B2 : ℂ) (t0 : ℝ) (z : ℂ) (l : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t - t0) ^ l * Real.log ‖z - (A2 + (t : ℂ) * (B2 - A2))‖

theorem BER_eq (A1 B1 A2 B2 : ℂ) (hu : B1 - A1 ≠ 0) (hv : B2 - A2 ≠ 0) (s0 t0 : ℝ)
    (hrel : A1 - A2 + (s0 : ℂ) * (B1 - A1) - (t0 : ℂ) * (B2 - A2) = 0) (k l : ℕ) :
    BER (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) k l
        (0 - s0) (1 - s0) (0 - t0) (1 - t0) =
      (1 - s0) ^ (k + 1) * P2 A2 B2 t0 (A1 + ((1 : ℝ) : ℂ) * (B1 - A1)) l
      - (0 - s0) ^ (k + 1) * P2 A2 B2 t0 (A1 + ((0 : ℝ) : ℂ) * (B1 - A1)) l
      + ((1 - t0) ^ (l + 1) * P2 A1 B1 s0 (A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) k
      - (0 - t0) ^ (l + 1) * P2 A1 B1 s0 (A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) k)
      - ((1 - s0) ^ (k + 1) - (0 - s0) ^ (k + 1)) * ((1 - t0) ^ (l + 1) - (0 - t0) ^ (l + 1))
        / (((k : ℝ) + 1) * ((l : ℝ) + 1)) := by
  unfold BER P2
  congr 1
  congr 1
  · -- first edge
    rw [← intervalIntegral.integral_comp_sub_right (fun t => (1 - s0) ^ (k + 1) * t ^ l *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (1 - s0) t
        - (0 - s0) ^ (k + 1) * t ^ l *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (0 - s0) t) t0]
    have hI : ∀ (zz : ℂ), IntervalIntegrable (fun t : ℝ => (t - t0) ^ l *
        Real.log ‖zz - (A2 + (t : ℂ) * (B2 - A2))‖) volume 0 1 := fun zz =>
      intervalIntegrable_pot A2 B2 zz hv (h := fun t => (t - t0) ^ l) (by fun_prop)
    have e : ∀ t : ℝ, (1 - s0) ^ (k + 1) * (t - t0) ^ l *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (1 - s0) (t - t0)
        - (0 - s0) ^ (k + 1) * (t - t0) ^ l *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (0 - s0) (t - t0)
        = (1 - s0) ^ (k + 1) * ((t - t0) ^ l * Real.log ‖(A1 + ((1 : ℝ) : ℂ) * (B1 - A1)) -
            (A2 + (t : ℂ) * (B2 - A2))‖)
          - (0 - s0) ^ (k + 1) * ((t - t0) ^ l * Real.log ‖(A1 + ((0 : ℝ) : ℂ) * (B1 - A1)) -
            (A2 + (t : ℂ) * (B2 - A2))‖) := by
      intro t
      rw [Lq_norm, Lq_norm, ← seg_diff A1 B1 A2 B2 s0 t0 hrel 1 t,
        ← seg_diff A1 B1 A2 B2 s0 t0 hrel 0 t]
      ring
    simp only [e]
    rw [intervalIntegral.integral_sub ((hI _).const_mul _) ((hI _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · -- second edge
    rw [← intervalIntegral.integral_comp_sub_right (fun s => s ^ k * (1 - t0) ^ (l + 1) *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) s (1 - t0)
        - s ^ k * (0 - t0) ^ (l + 1) *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) s (0 - t0)) s0]
    have hI : ∀ (zz : ℂ), IntervalIntegrable (fun s : ℝ => (s - s0) ^ k *
        Real.log ‖zz - (A1 + (s : ℂ) * (B1 - A1))‖) volume 0 1 := fun zz =>
      intervalIntegrable_pot A1 B1 zz hu (h := fun s => (s - s0) ^ k) (by fun_prop)
    have e : ∀ s : ℝ, (s - s0) ^ k * (1 - t0) ^ (l + 1) *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (s - s0) (1 - t0)
        - (s - s0) ^ k * (0 - t0) ^ (l + 1) *
        Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (s - s0) (0 - t0)
        = (1 - t0) ^ (l + 1) * ((s - s0) ^ k * Real.log ‖(A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) -
            (A1 + (s : ℂ) * (B1 - A1))‖)
          - (0 - t0) ^ (l + 1) * ((s - s0) ^ k * Real.log ‖(A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) -
            (A1 + (s : ℂ) * (B1 - A1))‖) := by
      intro s
      rw [Lq_norm, Lq_norm, ← norm_neg ((A2 + ((1 : ℝ) : ℂ) * (B2 - A2)) - _),
        ← norm_neg ((A2 + ((0 : ℝ) : ℂ) * (B2 - A2)) - _), neg_sub, neg_sub,
        seg_diff A1 B1 A2 B2 s0 t0 hrel s 1, seg_diff A1 B1 A2 B2 s0 t0 hrel s 0]
      ring
    simp only [e]
    rw [intervalIntegral.integral_sub ((hI _).const_mul _) ((hI _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end CatalanCore.Uniform.Decay.PairEnergy
