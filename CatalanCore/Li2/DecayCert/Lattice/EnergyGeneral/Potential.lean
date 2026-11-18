module
public import CatalanCore.Li2.DecayCert.Lattice.EnergyGeneral.Integrable
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem left_logPot_jet (μ : Measure ℂ) [IsFiniteMeasure μ] (y0 h : ℝ)
    (hy : y0<0) (hh : 0≤h) (hsep : h< -y0)
    (hs : μ {s | s.im≠0 ∨ s.re<0}=0)
    (hb : Integrable (fun s => Real.log ‖(y0:ℂ)-s‖) μ)
    (w : ℂ) (hw : ‖w-(y0:ℂ)‖≤h) (K : ℕ) :
    |U μ w-(U μ (y0:ℂ)+(∑ k∈Finset.range K,(w-(y0:ℂ))^(k+1)*
      (∫ s,(s-(y0:ℂ))^(-((k+1:ℕ):ℤ)) ∂μ)/(k+1:ℕ)).re)| ≤ mpErr (μ.real univ) (h/(-y0)) K := by
  let f : ℂ → ℂ := fun s => ∑ k∈Finset.range K,(w-(y0:ℂ))^(k+1)*(s-(y0:ℂ))^(-((k+1:ℕ):ℤ))/(k+1:ℕ)
  have hi (k : ℕ) : Integrable (fun s : ℂ => (w-(y0:ℂ))^(k+1)*(s-(y0:ℂ))^(-((k+1:ℕ):ℤ))/(k+1:ℕ)) μ :=
    ((left_inverse_integrable μ y0 hy hs k).const_mul _).div_const _
  have hif : Integrable f μ := integrable_finsetSum _ (fun k _ => hi k)
  have hfi : (∫ s,f s ∂μ)=∑ k∈Finset.range K,(w-(y0:ℂ))^(k+1)*
      (∫ s,(s-(y0:ℂ))^(-((k+1:ℕ):ℤ)) ∂μ)/(k+1:ℕ) := by
    dsimp only [f]
    rw [integral_finsetSum _ (fun k _ => hi k)]
    simp only [integral_div,integral_const_mul]
  have hil := (left_log_integrable_iff μ y0 h hy hh hsep hs w hw).mp hb
  let r : ℂ → ℝ := fun s => -Real.log ‖w-s‖+Real.log ‖(y0:ℂ)-s‖-(f s).re
  have hr : ∀ᵐ s ∂μ,‖r s‖≤(h/(-y0))^(K+1)/((K+1:ℕ)*(1-h/(-y0))) := by
    filter_upwards [left_source_ae μ hs] with s hs
    have hp := left_log_jet_point s w y0 h hy hh hsep hs.1 hs.2 hw K
    change |-Real.log ‖w-s‖+Real.log ‖(y0:ℂ)-s‖-(f s).re|≤_
    rw [show -Real.log ‖w-s‖+Real.log ‖(y0:ℂ)-s‖-(f s).re=
      -(Real.log ‖w-s‖-Real.log ‖(y0:ℂ)-s‖+(f s).re) by ring,abs_neg]
    exact hp
  have he : (∫ s,r s ∂μ)=U μ w-(U μ (y0:ℂ)+(∑ k∈Finset.range K,(w-(y0:ℂ))^(k+1)*
      (∫ s,(s-(y0:ℂ))^(-((k+1:ℕ):ℤ)) ∂μ)/(k+1:ℕ)).re) := by
    have e1 := integral_sub (hil.neg.add hb) hif.re
    have e2 := integral_add hil.neg hb
    simp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply,RCLike.re_to_complex] at e1 e2
    have hre := integral_re hif
    simp only [RCLike.re_to_complex] at hre
    dsimp only [r]
    rw [e1,e2,integral_neg,hre,hfi]
    simp only [U,P]
    ring
  have hbound := norm_integral_le_of_norm_le_const hr
  rw [he,Real.norm_eq_abs] at hbound
  exact hbound.trans_eq (by dsimp only [mpErr]; ring)
#print axioms left_logPot_jet
end
end CatalanCore.Li2.DecayCert
