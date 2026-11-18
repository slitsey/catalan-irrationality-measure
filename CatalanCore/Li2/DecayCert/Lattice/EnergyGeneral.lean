module
public import CatalanCore.Li2.DecayCert.Lattice.EnergyGeneral.Potential
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem energy_two_segments (σ1 σ2 : Measure ℂ) [IsFiniteMeasure σ1] [IsFiniteMeasure σ2]
    (y0 h : ℝ) (hh : 0≤h)
    (hs1 : σ1 {s | s.im≠0 ∨ s.re<0}=0)
    (hs2 : σ2 {s | h<‖s-(y0:ℂ)‖}=0) (hsep : h< -y0)
    (hlog : Integrable (fun xy : ℂ × ℂ => Real.log ‖xy.1-xy.2‖) ((σ1+σ2).prod (σ1+σ2))) (K : ℕ) :
    |I (σ1+σ2)-(I σ1+I σ2+2*(σ2.real univ*U σ1 (y0:ℂ)+
      (∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*
        (∫ s,(s-(y0:ℂ))^(-((k+1:ℕ):ℤ)) ∂σ1)/(k+1:ℕ)).re))| ≤
      2*σ2.real univ*mpErr (σ1.real univ) (h/(-y0)) K := by
  by_cases hn : σ2=0
  · subst σ2
    simp [I,U,P,moment]
  have hy : y0<0 := by linarith
  have hμ : σ1≤σ1+σ2 := le_add_of_nonneg_right (show (0:Measure ℂ)≤σ2 from bot_le)
  have hν : σ2≤σ1+σ2 := le_add_of_nonneg_left (show (0:Measure ℂ)≤σ1 from bot_le)
  have hc := hlog.mono_measure (Measure.prod_mono hν hμ)
  have hb := log_base_integrable_of_cross σ1 σ2 hn y0 h hy hh hsep hs1 hs2 hc
  have hiU : Integrable (U σ1) σ2 := hc.integral_prod_left.neg
  let a : ℕ → ℂ := fun k => ∫ s,(s-(y0:ℂ))^(-((k+1:ℕ):ℤ)) ∂σ1
  let f : ℂ → ℂ := fun w => ∑ k∈Finset.range K,(w-(y0:ℂ))^(k+1)*a k/(k+1:ℕ)
  have hi (k : ℕ) : Integrable (fun w : ℂ => (w-(y0:ℂ))^(k+1)*a k/(k+1:ℕ)) σ2 :=
    ((disk_moment_integrable σ2 y0 h hs2 (k+1)).mul_const _).div_const _
  have hif : Integrable f σ2 := integrable_finsetSum _ (fun k _ => hi k)
  have hfi : (∫ w,f w ∂σ2)=∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*a k/(k+1:ℕ) := by
    dsimp only [f]
    rw [integral_finsetSum _ (fun k _ => hi k)]
    simp only [integral_div,integral_mul_const,moment]
  let r : ℂ → ℝ := fun w => U σ1 w-(U σ1 (y0:ℂ)+(f w).re)
  have hr : ∀ᵐ w ∂σ2,‖r w‖≤mpErr (σ1.real univ) (h/(-y0)) K := by
    filter_upwards [disk_source_ae σ2 y0 h hs2] with w hw
    exact left_logPot_jet σ1 y0 h hy hh hsep hs1 hb w hw K
  have he : (∫ w,r w ∂σ2)=(∫ w,U σ1 w ∂σ2)-
      (σ2.real univ*U σ1 (y0:ℂ)+(∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*a k/(k+1:ℕ)).re) := by
    have e1 := integral_sub hiU ((integrable_const (U σ1 (y0:ℂ))).add hif.re)
    have e2 := integral_add (μ:=σ2) (integrable_const (U σ1 (y0:ℂ))) hif.re
    simp only [Pi.sub_apply,Pi.add_apply,RCLike.re_to_complex] at e1 e2
    have hre := integral_re hif
    simp only [RCLike.re_to_complex] at hre
    dsimp only [r]
    rw [e1,e2,integral_const,hre,hfi]
    simp only [smul_eq_mul]
  have hbound := norm_integral_le_of_norm_le_const hr
  rw [he,Real.norm_eq_abs] at hbound
  rw [energy_add_integrable_log σ1 σ2 hlog]
  have heq : I σ1+I σ2+2*(∫ w,U σ1 w ∂σ2)-
      (I σ1+I σ2+2*(σ2.real univ*U σ1 (y0:ℂ)+(∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*a k/(k+1:ℕ)).re))=
      2*((∫ w,U σ1 w ∂σ2)-(σ2.real univ*U σ1 (y0:ℂ)+(∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*a k/(k+1:ℕ)).re)) := by ring
  change |I σ1+I σ2+2*(∫ w,U σ1 w ∂σ2)-
      (I σ1+I σ2+2*(σ2.real univ*U σ1 (y0:ℂ)+(∑ k∈Finset.range K,moment σ2 (y0:ℂ) (k+1)*a k/(k+1:ℕ)).re))|≤_
  rw [heq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [hbound]
#print axioms energy_two_segments
end
end CatalanCore.Li2.DecayCert
