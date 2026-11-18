module
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.Defs
public import CatalanCore.Li2.DecayCert.Lattice.MultipoleUniform
public import CatalanCore.Li2.DecayCert.Compile.Basic
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert

private theorem source_real_ae (σ : Measure ℂ) (Y : ℝ)
    (hs : σ {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0) :
    ∀ᵐ s ∂σ, s.im=0 ∧ 0≤s.re ∧ s.re≤Y := by
  have h := (measure_eq_zero_iff_ae_notMem).mp hs
  filter_upwards [h] with s h
  simpa only [mem_ofPred_eq,not_or,not_not,not_lt] using h

private theorem left_log_integrable (σ : Measure ℂ) [IsFiniteMeasure σ]
    (Y x : ℝ) (hx : x<0)
    (hs : σ {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0) :
    Integrable (fun s => Real.log ‖(x:ℂ)-s‖) σ := by
  let S : Set ℂ := (fun t : ℝ => (t:ℂ)) '' Icc 0 Y
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hc : ContinuousOn (fun s : ℂ => Real.log ‖(x:ℂ)-s‖) S := by
    apply (continuous_const.sub continuous_id).norm.continuousOn.log
    rintro _ ⟨t,ht,rfl⟩
    apply norm_ne_zero_iff.mpr
    intro he
    have h := congrArg Complex.re he
    simp only [Pi.sub_apply,id_eq,Complex.sub_re,Complex.ofReal_re,Complex.zero_re] at h
    linarith [ht.1]
  apply (hc.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero
  filter_upwards [source_real_ae σ Y hs] with s h
  have he : s=(s.re:ℂ) := by apply Complex.ext <;> simp [h.1]
  intro hn
  exact (hn ⟨s.re,⟨h.2.1,h.2.2⟩,he.symm⟩).elim

private theorem inverse_power_integrable (σ : Measure ℂ) [IsFiniteMeasure σ]
    (Y y0 : ℝ) (hy : y0<0)
    (hs : σ {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0) (k : ℕ) :
    Integrable (fun s => (s.re-y0)^(-(k:ℤ))) σ := by
  let S : Set ℂ := (fun t : ℝ => (t:ℂ)) '' Icc 0 Y
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hc : ContinuousOn (fun s : ℂ => (s.re-y0)^(-(k:ℤ))) S := by
    simp only [zpow_neg,zpow_natCast]
    apply ((Complex.continuous_re.sub continuous_const).pow k).continuousOn.inv₀
    rintro _ ⟨t,ht,rfl⟩
    exact pow_ne_zero _ (ne_of_gt (by change 0<t-y0; linarith [ht.1]))
  apply (hc.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero
  filter_upwards [source_real_ae σ Y hs] with s h
  have he : s=(s.re:ℂ) := by apply Complex.ext <;> simp [h.1]
  intro hn
  exact (hn ⟨s.re,⟨h.2.1,h.2.2⟩,he.symm⟩).elim

private theorem real_left_norm (x : ℝ) (hx : x<0) (s : ℂ)
    (hs : s.im=0) (hs0 : 0≤s.re) : ‖(x:ℂ)-s‖=s.re-x := by
  have he : s=(s.re:ℂ) := by apply Complex.ext <;> simp [hs]
  rw [he,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith)]
  simp only [Complex.ofReal_re]
  ring

theorem log_stieltjes_point (t r u : ℝ) (ht : 0<t) (hr : 0≤r) (hrt : r<t)
    (hu : |u|≤r) (K : ℕ) :
    |-Real.log (t-u)+Real.log t-
      ∑ k ∈ Finset.range (K+1),t^(-(k:ℤ))*u^k/(k:ℝ)|≤
      (r/t)^(K+1)/((K+1:ℕ)*(1-r/t)) := by
  have hv : r/t<1 := (div_lt_one ht).mpr hrt
  have hw : |u/t|≤r/t := by rw [abs_div,abs_of_pos ht]; exact div_le_div_of_nonneg_right hu ht.le
  have hp : 0<1-u/t := by have h := (abs_le.mp hw).2; linarith
  have he : t-u=t*(1-u/t) := by field_simp <;> ring
  have hl : Real.log (t-u)=Real.log t+Real.log (1-u/t) := by
    rw [he,Real.log_mul ht.ne' hp.ne']
  have h := CatalanCore.Uniform.Decay.Tools.abs_log_add_logJet_le hw hv (m:=K+1) (by omega)
  have hsum : (∑ k ∈ Finset.range (K+1),t^(-(k:ℤ))*u^k/(k:ℝ))=
      ∑ k ∈ Finset.range (K+1),(u/t)^k/(k:ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [zpow_neg,zpow_natCast,div_pow]
    ring
  rw [hl,hsum]
  have heq : - (Real.log t+Real.log (1-u/t))+Real.log t-
      (∑ k ∈ Finset.range (K+1),(u/t)^k/(k:ℝ))=
      -(Real.log (1-u/t)+∑ k ∈ Finset.range (K+1),(u/t)^k/(k:ℝ)) := by ring
  rw [heq,abs_neg]
  exact h

#print axioms log_stieltjes_point
theorem evalModel_stieltjesCoeffs (σ : Measure ℂ) (y0 u : ℝ) (K : ℕ) :
    evalModel (stieltjesCoeffs σ y0 K) u=U σ (y0:ℂ)+
      ∑ k ∈ Finset.range (K+1), inverseMoment σ y0 k*u^k/(k:ℝ) := by
  rw [stieltjesCoeffs,evalModel_range]
  have he (k : ℕ) :
      (if k=0 then U σ (y0:ℂ) else inverseMoment σ y0 k/(k:ℝ))*u^k=
        (if k=0 then U σ (y0:ℂ) else 0)+inverseMoment σ y0 k*u^k/(k:ℝ) := by
    by_cases hk : k=0
    · subst k; simp
    · simp only [hk,ite_false]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem logPot_stieltjes_model (σ : Measure ℂ) [IsFiniteMeasure σ]
    (y0 r Y : ℝ) (hy : y0<0) (hr : 0≤r) (hY : 0≤Y) (hsep : r < -y0)
    (hs : σ {s | s.im ≠ 0 ∨ s.re<0 ∨ Y<s.re}=0) (K : ℕ) :
    Models (fun u => U σ ((y0+u:ℝ):ℂ)) (stieltjesCoeffs σ y0 K) r
      (mpErr (σ.real univ) (r/(-y0)) K) := by
  have hd : 0 < -y0 := neg_pos.mpr hy
  have hv : r/(-y0)<1 := (div_lt_one hd).mpr hsep
  have hv0 : 0≤r/(-y0) := div_nonneg hr hd.le
  have hden : 0<((K+1:ℕ):ℝ)*(1-r/(-y0)) := mul_pos (by positivity) (sub_pos.mpr hv)
  refine ⟨hr,div_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hv0 _)) hden.le,?_⟩
  intro u hu
  have hxu : y0+u<0 := by have := (abs_le.mp hu).2; linarith
  have hi0 := left_log_integrable σ Y y0 hy hs
  have hiu := left_log_integrable σ Y (y0+u) hxu hs
  let jet : ℂ→ℝ := fun s =>
    ∑ k ∈ Finset.range (K+1), (s.re-y0)^(-(k:ℤ))*u^k/(k:ℝ)
  have hij : Integrable jet σ := by
    apply integrable_finsetSum _
    intro k hk
    exact ((inverse_power_integrable σ Y y0 hy hs k).mul_const (u^k)).div_const _
  have hej : (∫ s, jet s ∂σ)=
      ∑ k ∈ Finset.range (K+1), inverseMoment σ y0 k*u^k/(k:ℝ) := by
    rw [show (∫ s, jet s ∂σ)=
      ∑ k ∈ Finset.range (K+1), ∫ s, (s.re-y0)^(-(k:ℤ))*u^k/(k:ℝ) ∂σ from
      integral_finsetSum _ (fun k hk =>
        ((inverse_power_integrable σ Y y0 hy hs k).mul_const (u^k)).div_const _)]
    simp only [integral_div,integral_mul_const,inverseMoment]
  let R : ℂ→ℝ := fun s => -Real.log ‖((y0+u:ℝ):ℂ)-s‖+
    Real.log ‖(y0:ℂ)-s‖-jet s
  have hbound : ∀ᵐ s ∂σ, ‖R s‖≤(r/(-y0))^(K+1)/((K+1:ℕ)*(1-r/(-y0))) := by
    filter_upwards [source_real_ae σ Y hs] with s h
    let t := s.re-y0
    have ht : 0<t := by dsimp [t]; linarith [h.2.1]
    have hdt : -y0≤t := by dsimp [t]; linarith [h.2.1]
    have hrt : r<t := hsep.trans_le hdt
    have hpt := log_stieltjes_point t r u ht hr hrt hu K
    have hrat : r/t≤r/(-y0) := div_le_div₀ hr le_rfl hd hdt
    have hm := mpErr_mono_ratio 1 (r/t) (r/(-y0)) K zero_le_one
      (div_nonneg hr ht.le) hrat hv
    have htail : (r/t)^(K+1)/((K+1:ℕ)*(1-r/t))≤
        (r/(-y0))^(K+1)/((K+1:ℕ)*(1-r/(-y0))) := by simpa only [mpErr,one_mul] using hm
    rw [Real.norm_eq_abs]
    dsimp only [R]
    rw [real_left_norm (y0+u) hxu s h.1 h.2.1,real_left_norm y0 hy s h.1 h.2.1]
    have harg : s.re-(y0+u)=t-u := by dsimp only [t]; ring
    rw [harg]
    exact hpt.trans htail
  have heR : (∫ s, R s ∂σ)=U σ ((y0+u:ℝ):ℂ)-U σ (y0:ℂ)-
      ∑ k ∈ Finset.range (K+1), inverseMoment σ y0 k*u^k/(k:ℝ) := by
    dsimp only [R]
    have hsub := integral_sub (μ:=σ)
      (f:=fun s : ℂ => -Real.log ‖((y0+u:ℝ):ℂ)-s‖+Real.log ‖(y0:ℂ)-s‖)
      (g:=jet) (hiu.neg.add hi0) hij
    have hadd := integral_add (μ:=σ)
      (f:=fun s : ℂ => -Real.log ‖((y0+u:ℝ):ℂ)-s‖)
      (g:=fun s : ℂ => Real.log ‖(y0:ℂ)-s‖) hiu.neg hi0
    rw [hsub,hadd,integral_neg,hej]
    simp only [U,P]
    ring
  have hb := norm_integral_le_of_norm_le_const hbound
  rw [heR,Real.norm_eq_abs] at hb
  rw [evalModel_stieltjesCoeffs]
  have he : U σ ((y0+u:ℝ):ℂ)-(U σ (y0:ℂ)+
      ∑ k ∈ Finset.range (K+1), inverseMoment σ y0 k*u^k/(k:ℝ))=
      U σ ((y0+u:ℝ):ℂ)-U σ (y0:ℂ)-
      ∑ k ∈ Finset.range (K+1), inverseMoment σ y0 k*u^k/(k:ℝ) := by ring
  rw [he]
  exact hb.trans_eq (by dsimp only [mpErr]; ring)

#print axioms evalModel_stieltjesCoeffs
#print axioms logPot_stieltjes_model
end CatalanCore.Li2.DecayCert
