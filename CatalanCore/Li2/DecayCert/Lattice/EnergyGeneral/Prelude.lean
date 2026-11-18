module
public import CatalanCore.Li2.DecayCert.Lattice.EnergyBilinear
public import CatalanCore.Li2.DecayCert.Multipole
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Uniform.Decay.Tools
noncomputable section

theorem energy_add_integrable_log (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hlog : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) ((μ+ν).prod (μ+ν))) :
    I (μ+ν)=I μ+I ν+2*(∫ u,U μ u ∂ν) := by
  have hμ : μ ≤ μ+ν := le_add_of_nonneg_right (show (0:Measure ℂ) ≤ ν from bot_le)
  have hν : ν ≤ μ+ν := le_add_of_nonneg_left (show (0:Measure ℂ) ≤ μ from bot_le)
  have hp (a b : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b]
      (ha : a ≤ μ+ν) (hb : b ≤ μ+ν) :
      Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (a.prod b) :=
    hlog.mono_measure (Measure.prod_mono ha hb)
  have hi (a b : Measure ℂ) [IsFiniteMeasure a] [IsFiniteMeasure b]
      (ha : a ≤ μ+ν) (hb : b ≤ μ+ν) : Integrable (U b) a := by
    change Integrable (fun u => -(∫ y,Real.log ‖u-y‖ ∂b)) a
    exact (hp a b ha hb).integral_prod_left.neg
  have hU : ∀ᵐ u : ℂ ∂(μ+ν),U (μ+ν) u=U μ u+U ν u := by
    filter_upwards [hlog.prod_right_ae] with u hu
    have hh := integrable_add_measure.mp hu
    change -(∫ y,Real.log ‖u-y‖ ∂(μ+ν))= -(∫ y,Real.log ‖u-y‖ ∂μ) + -(∫ y,Real.log ‖u-y‖ ∂ν)
    rw [integral_add_measure hh.1 hh.2]
    ring
  have hc : (∫ u,U ν u ∂μ)=∫ u,U μ u ∂ν := by
    change (∫ u,-(∫ y,Real.log ‖u-y‖ ∂ν) ∂μ)=∫ u,-(∫ y,Real.log ‖u-y‖ ∂μ) ∂ν
    rw [integral_neg,integral_neg]
    congr 1
    rw [integral_integral_swap (hp μ ν hμ hν)]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by simp only [norm_sub_rev])
  have him : Integrable (U μ) (μ+ν) := integrable_add_measure.mpr ⟨hi μ μ hμ hμ,hi ν μ hν hμ⟩
  have hin : Integrable (U ν) (μ+ν) := integrable_add_measure.mpr ⟨hi μ ν hμ hν,hi ν ν hν hν⟩
  change (∫ u,U (μ+ν) u ∂(μ+ν))=_
  rw [integral_congr_ae hU,integral_add him hin,
    integral_add_measure (hi μ μ hμ hμ) (hi ν μ hν hμ),
    integral_add_measure (hi μ ν hμ hν) (hi ν ν hν hν),hc]
  change I μ+(∫ u,U μ u ∂ν)+((∫ u,U μ u ∂ν)+I ν)=_
  ring

theorem left_log_jet_point (s w : ℂ) (y0 h : ℝ) (hy : y0 < 0) (hh : 0 ≤ h)
    (hsep : h < -y0) (hsim : s.im=0) (hsre : 0 ≤ s.re) (hw : ‖w-(y0:ℂ)‖ ≤ h) (K : ℕ) :
    |Real.log ‖w-s‖-Real.log ‖(y0:ℂ)-s‖+
      (∑ k ∈ Finset.range K,(w-(y0:ℂ))^(k+1)*(s-(y0:ℂ))^(-(k+1:ℤ))/(k+1:ℕ)).re| ≤
      (h/(-y0))^(K+1)/((K+1:ℕ)*(1-h/(-y0))) := by
  let t : ℝ := s.re-y0
  let q : ℂ := (w-(y0:ℂ))/(s-(y0:ℂ))
  have ht : 0 < t := by dsimp only [t]; linarith
  have hts : -y0 ≤ t := by dsimp only [t]; linarith
  have hsr : s=(s.re:ℂ) := by apply Complex.ext <;> simp [hsim]
  have hsn : ‖s-(y0:ℂ)‖=t := by
    rw [hsr,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  have hsne : s-(y0:ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hsn]; exact ht.ne')
  have hq : ‖q‖ ≤ h/(-y0) := by
    dsimp only [q]
    rw [norm_div,hsn]
    exact (div_le_div_of_nonneg_right hw ht.le).trans
      (div_le_div_of_nonneg_left hh (neg_pos.mpr hy) hts)
  have hv : h/(-y0) < 1 := (div_lt_one (neg_pos.mpr hy)).mpr hsep
  have h1q : 1-q ≠ 0 := by
    intro he
    have hqe : q=1 := (sub_eq_zero.mp he).symm
    rw [hqe,norm_one] at hq
    linarith
  have hfactor : w-s= -(s-(y0:ℂ))*(1-q) := by
    dsimp only [q]
    field_simp [hsne]
    ring
  have hlog : Real.log ‖w-s‖=Real.log ‖(y0:ℂ)-s‖+Real.log ‖1-q‖ := by
    rw [hfactor,norm_mul,norm_neg,Real.log_mul (norm_ne_zero_iff.mpr hsne) (norm_ne_zero_iff.mpr h1q),norm_sub_rev s (y0:ℂ)]
  have hj : logJet (K+1) q=∑ k ∈ Finset.range K,
      (w-(y0:ℂ))^(k+1)*(s-(y0:ℂ))^(-(k+1:ℤ))/(k+1:ℕ) := by
    rw [logJet,Finset.sum_range_succ']
    simp only [pow_zero,Nat.cast_zero,div_zero,add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [q]
    rw [show (k+1:ℤ)=((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,div_pow]
    ring
  have hb := norm_log_add_logJet_le hq hv (m:=K+1) (by omega)
  have hre := (Complex.abs_re_le_norm (Complex.log (1-q)+logJet (K+1) q)).trans hb
  rw [hj,Complex.add_re,Complex.log_re] at hre
  rw [hlog]
  convert hre using 1 <;> ring
#print axioms energy_add_integrable_log
#print axioms left_log_jet_point
end
end CatalanCore.Li2.DecayCert
