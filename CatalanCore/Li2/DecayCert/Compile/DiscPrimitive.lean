module
public import CatalanCore.Li2.DecayCert.Compile.DiscLog
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem segment_disc_primitive_exists (d : SegmentData) (ζ γ : ℂ) (R : ℝ) (hR : 0 < R)
    (hoff : ∀ u ∈ Metric.ball (0:ℂ) R, 1 < jc (ζ+γ*u)) :
    ∃ G : ℂ → ℂ, IsDiscSegmentPrimitive d ζ γ R G ∧
      AnalyticOnNhd ℂ G (Metric.ball 0 R) ∧ ∃ b : ℕ → ℂ, HasTaylorSeriesAt G b 0 := by
  let jp : ℂ → ℂ := fun u => jphi (ζ+γ*u)
  have hja : AnalyticOnNhd ℂ jp (Metric.ball 0 R) := by
    apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
    intro u hu
    have hc : HasDerivAt (fun v : ℂ => ζ+γ*v) γ u := by
      simpa using (hasDerivAt_id' u).const_mul γ |>.const_add ζ
    exact ((hasDerivAt_jphi (hoff u hu)).comp u hc).differentiableAt.differentiableWithinAt
  have hzero : 1 < jc ζ := by simpa using hoff 0 (Metric.mem_ball_self hR)
  let f : ℂ → ℂ := fun u => jp u/2
  have hfa : AnalyticOnNhd ℂ f (Metric.ball 0 R) := by
    intro u hu
    exact (hja u hu).div_const
  have hne (u : ℂ) (hu : u ∈ Metric.ball (0:ℂ) R) : f u ≠ 0 :=
    div_ne_zero (jphi_ne_zero (hoff u hu)) (by norm_num)
  have hB : Complex.exp (Complex.log (jphi ζ/2))=f 0 := by
    dsimp [f,jp]
    rw [mul_zero,add_zero,Complex.exp_log (div_ne_zero (jphi_ne_zero hzero) (by norm_num))]
  rcases analytic_log_on_ball f (deriv f) R hR hfa hfa.deriv
    (fun u hu => (hfa u hu).differentiableAt.hasDerivAt) hne _ hB with ⟨L,hLa,hL0,hLexp⟩
  let G : ℂ → ℂ := fun u => (d.c 0:ℂ)*L u-
    ∑ k ∈ Finset.range d.N, (d.c (k+1):ℂ)*(jp u)⁻¹^(k+1)/(k+1:ℕ)
  have hGa : AnalyticOnNhd ℂ G (Metric.ball 0 R) := by
    intro u hu
    have hj : AnalyticAt ℂ jp u := hja u hu
    have hl : AnalyticAt ℂ L u := hLa u hu
    have hn : jp u ≠ 0 := jphi_ne_zero (hoff u hu)
    dsimp only [G]
    fun_prop (disch := assumption)
  refine ⟨G,⟨L,hLa,hL0,?_⟩,hGa,?_⟩
  · intro u hu
    exact ⟨hoff u hu,hLexp u hu,rfl⟩
  · rcases hGa 0 (Metric.mem_ball_self hR) with ⟨p,hp⟩
    exact ⟨fun n => p.coeff n,hasTaylorSeriesAt_of_hasFPowerSeriesAt hp⟩

#print axioms segment_disc_primitive_exists
end
end CatalanCore.Li2.DecayCert
