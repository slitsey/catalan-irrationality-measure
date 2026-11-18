module
public import CatalanCore.Li2.DecayCert.Holder.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexEnergy
open CatalanCore.Decay.ComplexContour CatalanCore.Lai.DecayInstance
noncomputable section

theorem continuous_P_of_ballMaj (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A : ℝ) (hσ : BallMajA σ b A (1/2)) : Continuous (P σ) := by
  apply continuous_iff_continuousAt.2
  intro u
  have hc : Continuous (fun v : ℂ => (4*A+σ.real univ)*‖v-u‖^((1:ℝ)/3)) := by
    apply continuous_const.mul
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).rpow_const (fun _ => Or.inr (by norm_num))
  have hlim : Tendsto (fun v : ℂ => (4*A+σ.real univ)*‖v-u‖^((1:ℝ)/3)) (nhds u) (nhds 0) := by
    simpa using hc.tendsto u
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro v
    simpa only [Real.dist_eq,P,potC] using ballMajA_potential_holder_third σ b A hσ v u
  · exact hlim

theorem SegmentData.continuous_P (d : SegmentData) (hpos : d.densityNonneg) : Continuous (P d.ν) := by
  haveI : IsFiniteMeasure d.ν := CatalanCore.Lai.DecayEnergy.isFiniteMeasure_seg hpos
  have hp := ballMajA_sig2 (M:=d.M) d.h_ne d.c d.N
  have hball : BallMajA d.ν (‖d.M‖+‖d.h‖+1) (2*(∑ k ∈ Finset.range (d.N+1),|d.c k|)/Real.sqrt ‖d.h‖) (1/2) := by
    refine ⟨by linarith [norm_nonneg d.M,norm_nonneg d.h],hp.A_nonneg,hp.α_pos,?_,?_⟩
    · exact segMeasure_compl (by linarith [norm_nonneg d.M,norm_nonneg d.h])
    · intro c r hr
      apply le_trans _ (hp.maj c r hr)
      rw [sig2,Measure.add_apply]
      exact le_add_of_nonneg_right (show (0:ENNReal) ≤ _ from bot_le)
  exact continuous_P_of_ballMaj d.ν _ _ hball

def segmentPathDerivative (d : SegmentData) (b e : ℂ) (t : ℝ) : ℝ :=
  ((e/d.h)*((fpoly d.c d.N).eval ((b+e*(t:ℂ)-d.M)/d.h)/jq ((b+e*(t:ℂ)-d.M)/d.h)-
    (rpoly d.c d.N).eval ((b+e*(t:ℂ)-d.M)/d.h))).re

theorem SegmentData.potential_path_hasDerivAt (d : SegmentData) (hpos : d.densityNonneg)
    (b e : ℂ) (t : ℝ) (hs : 1 < jc ((b+e*(t:ℂ)-d.M)/d.h)) :
    HasDerivAt (fun v : ℝ => P d.ν (b+e*(v:ℂ))) (segmentPathDerivative d b e t) t := by
  let ζ := (b+e*(t:ℂ)-d.M)/d.h
  let γ := e/d.h
  have hcont : Continuous (fun v : ℂ => ζ+γ*v) := by fun_prop
  have hn : {v : ℂ | 1 < jc (ζ+γ*v)} ∈ nhds 0 :=
    (isOpen_jc.preimage hcont).mem_nhds (by simpa using hs)
  rcases Metric.mem_nhds_iff.mp hn with ⟨R,hR,hball⟩
  rcases segment_disc_primitive_exists d ζ γ R hR (fun v hv => hball hv) with ⟨G,hG,hGa,bcoef,hbc⟩
  have hD : HasDerivAt G (γ*((fpoly d.c d.N).eval ζ/jq ζ-(rpoly d.c d.N).eval ζ)) (0:ℂ) := by
    simpa only [mul_zero,add_zero] using discPrimitive_hasDerivAt d ζ γ R G hG 0 (Metric.mem_ball_self hR)
  have hDr : HasDerivAt (fun v : ℝ => (G (v:ℂ)).re)
      (γ*((fpoly d.c d.N).eval ζ/jq ζ-(rpoly d.c d.N).eval ζ)).re (t-t) := by
    simpa using hD.real_of_complex
  have hh := (hDr.comp t (h:=fun v : ℝ => v-t) ((hasDerivAt_id' t).sub_const t)).const_add (d.c 0*Real.log ‖d.h‖)
  have he : (fun v : ℝ => P d.ν (b+e*(v:ℂ))) =ᶠ[nhds t]
      (fun v : ℝ => d.c 0*Real.log ‖d.h‖+(G ((v-t:ℝ):ℂ)).re) := by
    filter_upwards [Metric.ball_mem_nhds t hR] with v hv
    have hvr : ((v-t:ℝ):ℂ) ∈ Metric.ball (0:ℂ) R := by
      simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev,Complex.norm_real,Real.norm_eq_abs,sub_zero] using hv
    have hp := discPrimitive_potential d hpos ζ γ R G hG _ hvr
    have hpoint : d.M+d.h*(ζ+γ*((v-t:ℝ):ℂ))=b+e*(v:ℂ) := by
      dsimp only [ζ,γ]
      push_cast
      field_simp [d.h_ne] <;> ring
    rwa [hpoint] at hp
  have hfinal := hh.congr_of_eventuallyEq he
  simpa only [mul_one,Function.comp_def,segmentPathDerivative,ζ,γ] using hfinal
#print axioms continuous_P_of_ballMaj
#print axioms SegmentData.continuous_P
#print axioms SegmentData.potential_path_hasDerivAt
end
end CatalanCore.Li2.DecayCert
