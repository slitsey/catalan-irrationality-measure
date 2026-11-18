module
public import CatalanCore.Li2.DecayCert.Compile.TaylorModel
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem discPrimitive_re_eq (d : SegmentData) (ζ γ : ℂ) (R : ℝ) (G : ℂ → ℂ)
    (hG : IsDiscSegmentPrimitive d ζ γ R G) (u : ℂ) (hu : u ∈ Metric.ball (0:ℂ) R) :
    (G u).re=(Gfun d.c d.N (ζ+γ*u)).re := by
  rcases hG with ⟨L,hLa,hL0,hL⟩
  rcases hL u hu with ⟨hs,he,hv⟩
  have hr : (L u).re=(Complex.log (jphi (ζ+γ*u)/2)).re := by
    rw [Complex.log_re,← he,Complex.norm_exp,Real.log_exp]
  rw [hv]
  simp only [Gfun,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hr]

theorem discPrimitive_potential (d : SegmentData) (hpos : d.densityNonneg)
    (ζ γ : ℂ) (R : ℝ) (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G)
    (u : ℂ) (hu : u ∈ Metric.ball (0:ℂ) R) :
    P d.ν (d.M+d.h*(ζ+γ*u))=d.c 0*Real.log ‖d.h‖+(G u).re := by
  have hz : (d.M+d.h*(ζ+γ*u)-d.M)/d.h=ζ+γ*u := by field_simp [d.h_ne] <;> ring
  have hs := hG.choose_spec.2.2 u hu
  rw [segPot_closed d hpos _ (by rw [hz]; exact hs.1),hz,discPrimitive_re_eq d ζ γ R G hG u hu]

theorem discPrimitive_seed (d : SegmentData) (ζ γ : ℂ) (R : ℝ) (hR : 0 < R)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G) :
    G 0=Gfun d.c d.N ζ := by
  rcases hG with ⟨L,hLa,hL0,hL⟩
  have he := (hL 0 (Metric.mem_ball_self hR)).2.2
  simpa only [mul_zero,add_zero,hL0,Gfun] using he

theorem inverse_jq_hasTaylor_exists (ζ γ : ℂ) (hs : 1 < jc ζ) :
    ∃ y : ℕ → ℂ, HasTaylorSeriesAt (fun u => (jq (ζ+γ*u))⁻¹) y 0 := by
  have ha : AnalyticAt ℂ (fun u => (jq (ζ+γ*u))⁻¹) 0 := by
    have hd : DifferentiableOn ℂ jq {z : ℂ | 1 < jc z} := by
      intro z hz
      exact (hasDerivAt_jq hz).differentiableAt.differentiableWithinAt
    have hq : AnalyticAt ℂ jq ζ := hd.analyticAt (isOpen_jc.mem_nhds hs)
    have hc : AnalyticAt ℂ (fun u : ℂ => ζ+γ*u) 0 := by fun_prop
    have hq' : AnalyticAt ℂ jq (ζ+γ*0) := by simpa using hq
    have hh : AnalyticAt ℂ (fun u : ℂ => jq (ζ+γ*u)) 0 := AnalyticAt.comp (f:=fun u : ℂ => ζ+γ*u) hq' hc
    exact hh.inv (by simpa using jq_ne_zero hs)
  rcases ha with ⟨p,hp⟩
  exact ⟨fun n => p.coeff n,hasTaylorSeriesAt_of_hasFPowerSeriesAt hp⟩
#print axioms discPrimitive_re_eq
#print axioms discPrimitive_potential
#print axioms discPrimitive_seed
#print axioms inverse_jq_hasTaylor_exists
end
end CatalanCore.Li2.DecayCert
