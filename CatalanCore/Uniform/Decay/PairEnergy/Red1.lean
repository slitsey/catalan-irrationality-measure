module

public import CatalanCore.Uniform.Decay.PairEnergy.Cont
public import CatalanCore.Uniform.Decay.Corners.Collinear

@[expose] public section

/-!
# Pair energy as a boundary-energy sum, first reduction (lane D, package D6c)

Two segments `p₁(s) = A₁ + s (B₁-A₁)`, `p₂(t) = A₂ + t (B₂-A₂)` with a common point
`p₁(s₀) = p₂(t₀)`.  In the centred variables `S = s - s₀`, `T = t - t₀`:
`p₁(s) - p₂(t) = S u - T v`, `‖S u - T v‖ = exp (Lq |u|² (-u·v) |v|² S T)`.  The iterated integral of
`S^k T^l log ‖p₁ - p₂‖` over `[0,1]²` is `BEL` on `[-s₀, 1-s₀] × [-t₀, 1-t₀]`.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Tools
  CatalanCore.Uniform.Decay.Corners CatalanCore.Uniform.Decay.Assembly

/-- The quadratic form of the pair, `(|u|², -u·v, |v|²)`. -/
def formA (u : ℂ) : ℝ := u.re ^ 2 + u.im ^ 2
def formB (u v : ℂ) : ℝ := -(u.re * v.re + u.im * v.im)
def formC (v : ℂ) : ℝ := v.re ^ 2 + v.im ^ 2

theorem Lq_norm (u v : ℂ) (S T : ℝ) :
    Lq (formA u) (formB u v) (formC v) S T = Real.log ‖(S : ℂ) * u - (T : ℂ) * v‖ := by
  unfold Lq formA formB formC
  rw [qf_eq_sq]
  have : ‖(S : ℂ) * u - (T : ℂ) * v‖ ^ 2 = (S * u.re - T * v.re) ^ 2 + (S * u.im - T * v.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [← this, Real.log_pow]; push_cast; ring

/-- Difference of the two segment points in centred variables. -/
theorem seg_diff (A1 B1 A2 B2 : ℂ) (s0 t0 : ℝ)
    (hrel : A1 - A2 + (s0 : ℂ) * (B1 - A1) - (t0 : ℂ) * (B2 - A2) = 0) (s t : ℝ) :
    (A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))
      = ((s - s0 : ℝ) : ℂ) * (B1 - A1) - ((t - t0 : ℝ) : ℂ) * (B2 - A2) := by
  push_cast; linear_combination hrel

/-- The `(k,l)` iterated integral over the unit square. -/
noncomputable def Ikl (A1 B1 A2 B2 : ℂ) (s0 t0 : ℝ) (k l : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, (s - s0) ^ k * (t - t0) ^ l *
    Real.log ‖(A1 + (s : ℂ) * (B1 - A1)) - (A2 + (t : ℂ) * (B2 - A2))‖

theorem Ikl_eq_BEL (A1 B1 A2 B2 : ℂ) (s0 t0 : ℝ)
    (hrel : A1 - A2 + (s0 : ℂ) * (B1 - A1) - (t0 : ℂ) * (B2 - A2) = 0) (k l : ℕ) :
    Ikl A1 B1 A2 B2 s0 t0 k l =
      BEL (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) k l
        (0 - s0) (1 - s0) (0 - t0) (1 - t0) := by
  unfold Ikl BEL
  rw [← intervalIntegral.integral_comp_sub_right (fun S => ∫ T in (0 - t0)..(1 - t0),
    S ^ k * T ^ l * Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) S T) s0]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← intervalIntegral.integral_comp_sub_right (fun T =>
    (s - s0) ^ k * T ^ l * Lq (formA (B1 - A1)) (formB (B1 - A1) (B2 - A2)) (formC (B2 - A2)) (s - s0) T) t0]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [Lq_norm, seg_diff A1 B1 A2 B2 s0 t0 hrel]

end CatalanCore.Uniform.Decay.PairEnergy
