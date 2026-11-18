module
public import CatalanCore.Li2.DecayCert.Compile.Elementary
public import CatalanCore.Li2.DecayCert.Series
public import Mathlib.Analysis.Complex.HasPrimitives
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem analytic_log_on_ball (f f' : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hf' : AnalyticOnNhd ℂ f' (Metric.ball 0 R))
    (hderiv : ∀ u ∈ Metric.ball (0:ℂ) R, HasDerivAt f (f' u) u)
    (hne : ∀ u ∈ Metric.ball (0:ℂ) R, f u ≠ 0)
    (B : ℂ) (hB : Complex.exp B=f 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (Metric.ball 0 R) ∧ L 0=B ∧
      (∀ u ∈ Metric.ball (0:ℂ) R, Complex.exp (L u)=f u) := by
  have hd : DifferentiableOn ℂ (fun u => f' u/f u) (Metric.ball (0:ℂ) R) := by
    intro u hu
    exact ((hf' u hu).differentiableAt.div (hf u hu).differentiableAt (hne u hu)).differentiableWithinAt
  rcases hd.isExactOn_ball.with_val_at 0 B with ⟨L,hL0,hL⟩
  have hLd : DifferentiableOn ℂ L (Metric.ball 0 R) := fun u hu => (hL u hu).differentiableAt.differentiableWithinAt
  have hLa : AnalyticOnNhd ℂ L (Metric.ball 0 R) := DifferentiableOn.analyticOnNhd hLd Metric.isOpen_ball
  let q : ℂ → ℂ := fun u => Complex.exp (L u)/f u
  have hq (u : ℂ) (hu : u ∈ Metric.ball (0:ℂ) R) : HasDerivAt q 0 u := by
    have hh := ((hL u hu).cexp).div (hderiv u hu) (hne u hu)
    convert hh using 1
    field_simp [hne u hu] <;> ring
  have hqc : DifferentiableOn ℂ q (Metric.ball 0 R) := fun u hu => (hq u hu).differentiableAt.differentiableWithinAt
  have hqd : (Metric.ball (0:ℂ) R).EqOn (deriv q) 0 := fun u hu => (hq u hu).deriv
  refine ⟨L,hLa,hL0,?_⟩
  intro u hu
  have he := IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball (0:ℂ) R).isPreconnected hqc hqd hu (Metric.mem_ball_self hR)
  have hq0 : q 0=1 := by dsimp [q]; rw [hL0,hB,div_self (hne 0 (Metric.mem_ball_self hR))]
  rw [hq0] at he
  exact (div_eq_one_iff_eq (hne u hu)).mp he

#print axioms analytic_log_on_ball
end
end CatalanCore.Li2.DecayCert
