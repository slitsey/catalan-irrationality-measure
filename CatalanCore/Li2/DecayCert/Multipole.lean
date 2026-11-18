module
public import CatalanCore.Li2.DecayCert.Segment
public import CatalanCore.Decay.Rect.Nodes
public import CatalanCore.Uniform.Decay.Tools.LogJet
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Topology
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert
noncomputable def moment (σ : Measure ℂ) (y0 : ℂ) (k : ℕ) : ℂ :=
  ∫ y, (y-y0)^k ∂σ
noncomputable def mp (σ : Measure ℂ) (y0 s : ℂ) (K : ℕ) : ℝ :=
  -σ.real univ*Real.log ‖s-y0‖ +
    (∑ k ∈ Finset.range K, moment σ y0 (k+1)/((k+1:ℕ)*(s-y0)^(k+1))).re
noncomputable def mpErr (m v : ℝ) (K : ℕ) : ℝ := m*v^(K+1)/((K+1:ℕ)*(1-v))
private theorem support_right (σ : Measure ℂ) (Y : ℝ)
    (hs : σ {s | s.im ≠ 0 ∨ s.re < 0 ∨ Y < s.re}=0) :
    ∀ᵐ y ∂σ, y.im=0 ∧ 0 ≤ y.re ∧ y.re ≤ Y := by
  have h := (measure_eq_zero_iff_ae_notMem).mp hs
  filter_upwards [h] with y hy
  simpa only [mem_ofPred_eq, not_or, not_not, not_lt] using hy

private theorem integrable_log_right (σ : Measure ℂ) [IsFiniteMeasure σ] (Y x : ℝ)
    (hs : σ {s | s.im ≠ 0 ∨ s.re < 0 ∨ Y < s.re}=0) (hx : Y < x) :
    Integrable (fun y => Real.log ‖(x:ℂ)-y‖) σ := by
  let S : Set ℂ := (fun t : ℝ => (t:ℂ)) '' Icc 0 Y
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hc : ContinuousOn (fun y : ℂ => Real.log ‖(x:ℂ)-y‖) S := by
    apply (continuous_const.sub continuous_id).norm.continuousOn.log
    rintro _ ⟨t, ht, rfl⟩
    apply norm_ne_zero_iff.mpr
    intro he
    have h := congrArg Complex.re he
    simp only [Pi.sub_apply, id_eq, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at h
    linarith [ht.2]
  apply (hc.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero
  filter_upwards [support_right σ Y hs] with y hy
  intro hn
  exfalso
  apply hn
  refine ⟨y.re, ⟨hy.2.1,hy.2.2⟩, ?_⟩
  apply Complex.ext <;> simp [hy.1]

theorem logPot_antitone_right (σ : Measure ℂ) [IsFiniteMeasure σ] (Y : ℝ)
    (hs : σ {s | s.im ≠ 0 ∨ s.re < 0 ∨ Y < s.re}=0) :
    AntitoneOn (fun x : ℝ => U σ (x:ℂ)) (Ioi Y) := by
  intro x hx z hz hxz
  unfold U P
  apply neg_le_neg
  apply integral_mono_ae (integrable_log_right σ Y x hs hx)
    (integrable_log_right σ Y z hs hz)
  filter_upwards [support_right σ Y hs] with y hy
  have h := CatalanCore.Decay.elog_real_anti (σ := y) (lt_of_le_of_lt hy.2.2 hx) hxz
  unfold CatalanLambda.Decay.elog at h
  rw [norm_sub_rev y (x:ℂ), norm_sub_rev y (z:ℂ)] at h
  linarith

theorem logPot_antitone_right_closed (σ : Measure ℂ) [IsFiniteMeasure σ] (Y : ℝ)
    (hs : σ {s | s.im ≠ 0 ∨ s.re < 0 ∨ Y < s.re}=0)
    (hno : σ {(Y:ℂ)}=0)
    (hintY : Integrable (fun y => Real.log ‖(Y:ℂ)-y‖) σ) :
    AntitoneOn (fun x : ℝ => U σ (x:ℂ)) (Ici Y) := by
  have hint (x : ℝ) (hx : Y ≤ x) : Integrable (fun y => Real.log ‖(x:ℂ)-y‖) σ := by
    rcases eq_or_lt_of_le hx with h | h
    · simpa only [h] using hintY
    · exact integrable_log_right σ Y x hs h
  intro x hx z hz hxz
  unfold U P
  apply neg_le_neg
  apply integral_mono_ae (hint x hx) (hint z hz)
  have hne := (measure_eq_zero_iff_ae_notMem).mp hno
  filter_upwards [support_right σ Y hs, hne] with y hy hyne
  have hlt : y.re < Y := by
    apply lt_of_le_of_ne hy.2.2
    intro he
    apply hyne
    apply Complex.ext <;> simp [he, hy.1]
  have h := CatalanCore.Decay.elog_real_anti (σ := y) (hlt.trans_le hx) hxz
  unfold CatalanLambda.Decay.elog at h
  rw [norm_sub_rev y (x:ℂ), norm_sub_rev y (z:ℂ)] at h
  linarith


private theorem logJet_shift (K : ℕ) (w : ℂ) :
    CatalanCore.Uniform.Decay.Tools.logJet (K+1) w =
      ∑ k ∈ Finset.range K, w^(k+1)/(k+1:ℕ) := by
  unfold CatalanCore.Uniform.Decay.Tools.logJet
  rw [Finset.sum_range_succ']
  simp

private theorem multipole_point (y y0 s : ℂ) (v : ℝ) (hv : v < 1)
    (hs : s-y0 ≠ 0) (hy : ‖(y-y0)/(s-y0)‖ ≤ v) (K : ℕ) :
    |Real.log ‖s-y‖ - Real.log ‖s-y0‖ +
      (∑ k ∈ Finset.range K, (y-y0)^(k+1)/((k+1:ℕ)*(s-y0)^(k+1))).re| ≤
      v^(K+1)/((K+1:ℕ)*(1-v)) := by
  let w : ℂ := (y-y0)/(s-y0)
  have hw : ‖w‖ < 1 := hy.trans_lt hv
  have hone : 1-w ≠ 0 := by
    intro he
    have : w=1 := by linear_combination -he
    simp [this] at hw
  have hfact : s-y=(s-y0)*(1-w) := by dsimp [w]; field_simp [hs]; ring
  have hlog : Real.log ‖s-y‖ = Real.log ‖s-y0‖ + Real.log ‖1-w‖ := by
    rw [hfact, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hs)
      (norm_ne_zero_iff.mpr hone)]
  have hjet : CatalanCore.Uniform.Decay.Tools.logJet (K+1) w =
      ∑ k ∈ Finset.range K, (y-y0)^(k+1)/((k+1:ℕ)*(s-y0)^(k+1)) := by
    rw [logJet_shift]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [w]
    rw [div_pow, div_div, mul_comm ((s-y0)^(k+1)) ((k+1:ℕ):ℂ)]
  have htail := CatalanCore.Uniform.Decay.Tools.norm_log_add_logJet_le hy hv
    (m := K+1) (by omega)
  have hre := Complex.abs_re_le_norm
    (Complex.log (1-w)+CatalanCore.Uniform.Decay.Tools.logJet (K+1) w)
  change ‖Complex.log (1-w)+CatalanCore.Uniform.Decay.Tools.logJet (K+1) w‖ ≤ _ at htail
  rw [hjet] at htail
  rw [Complex.add_re, Complex.log_re, hjet] at hre
  calc
    _ = |Real.log ‖1-w‖ +
        (∑ k ∈ Finset.range K, (y-y0)^(k+1)/((k+1:ℕ)*(s-y0)^(k+1))).re| := by
      rw [hlog]
      congr 1
      ring
    _ ≤ _ := hre.trans htail

private theorem integrable_moment_power (σ : Measure ℂ) [IsFiniteMeasure σ]
    (y0 : ℂ) (h : ℝ) (hh : 0 ≤ h) (hsupp : σ {y | h < ‖y-y0‖}=0) (k : ℕ) :
    Integrable (fun y => (y-y0)^k) σ := by
  apply Integrable.mono' (integrable_const (h^k)) (by fun_prop)
  have hae := (measure_eq_zero_iff_ae_notMem).mp hsupp
  filter_upwards [hae] with y hy
  have hy' : ‖y-y0‖ ≤ h := by simpa using hy
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hy' _

private theorem integrable_log_ball (σ : Measure ℂ) [IsFiniteMeasure σ]
    (y0 s : ℂ) (h : ℝ) (hsupp : σ {y | h < ‖y-y0‖}=0)
    (hsep : h < ‖s-y0‖) : Integrable (fun y => Real.log ‖s-y‖) σ := by
  have hc : ContinuousOn (fun y : ℂ => Real.log ‖s-y‖) (Metric.closedBall y0 h) := by
    apply (continuous_const.sub continuous_id).norm.continuousOn.log
    intro y hy
    apply norm_ne_zero_iff.mpr
    intro he
    have hys : s=y := sub_eq_zero.mp he
    subst s
    have hy' : ‖y-y0‖ ≤ h := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    linarith
  apply (hc.integrableOn_compact (isCompact_closedBall y0 h)).integrable_of_ae_notMem_eq_zero
  have hae := (measure_eq_zero_iff_ae_notMem).mp hsupp
  filter_upwards [hae] with y hy
  intro hn
  exfalso
  apply hn
  simpa only [Metric.mem_closedBall, dist_eq_norm, mem_ofPred_eq, not_lt] using hy


theorem logPot_multipole (σ : Measure ℂ) [IsFiniteMeasure σ] (y0 s : ℂ)
    (h : ℝ) (hh : 0 ≤ h) (hsupp : σ {y | h < ‖y-y0‖}=0)
    (hsep : h < ‖s-y0‖) (K : ℕ) :
    |U σ s-mp σ y0 s K| ≤ mpErr (σ.real univ) (h/‖s-y0‖) K := by
  have hn : 0 < ‖s-y0‖ := hh.trans_lt hsep
  have hs : s-y0 ≠ 0 := norm_ne_zero_iff.mp hn.ne'
  let v : ℝ := h/‖s-y0‖
  have hv : v < 1 := (div_lt_one hn).mpr hsep
  let f : ℂ → ℂ := fun y =>
    ∑ k ∈ Finset.range K, (y-y0)^(k+1)/((k+1:ℕ)*(s-y0)^(k+1))
  have hi (k : ℕ) : Integrable
      (fun y => (y-y0)^(k+1)/((k+1:ℕ)*(s-y0)^(k+1))) σ :=
    (integrable_moment_power σ y0 h hh hsupp (k+1)).div_const _
  have hif : Integrable f σ := by
    exact integrable_finsetSum _ (fun k _ => hi k)
  have hfi : (∫ y, f y ∂σ) =
      ∑ k ∈ Finset.range K, moment σ y0 (k+1)/((k+1:ℕ)*(s-y0)^(k+1)) := by
    dsimp only [f]
    rw [integral_finsetSum _ (fun k _ => hi k)]
    simp only [integral_div, moment]
  have hil : Integrable (fun y => Real.log ‖s-y‖) σ :=
    integrable_log_ball σ y0 s h hsupp hsep
  let R : ℂ → ℝ := fun y => -Real.log ‖s-y‖ - (-Real.log ‖s-y0‖+(f y).re)
  have hb : ∀ᵐ y ∂σ, ‖R y‖ ≤ v^(K+1)/((K+1:ℕ)*(1-v)) := by
    have hae := (measure_eq_zero_iff_ae_notMem).mp hsupp
    filter_upwards [hae] with y hy
    have hy' : ‖y-y0‖ ≤ h := by simpa using hy
    have hw : ‖(y-y0)/(s-y0)‖ ≤ v := by
      rw [norm_div]
      exact div_le_div_of_nonneg_right hy' (norm_nonneg _)
    have ht := multipole_point y y0 s v hv hs hw K
    change |-Real.log ‖s-y‖ - (-Real.log ‖s-y0‖+(f y).re)| ≤ _
    rw [show -Real.log ‖s-y‖ - (-Real.log ‖s-y0‖+(f y).re) =
      -(Real.log ‖s-y‖-Real.log ‖s-y0‖+(f y).re) by ring, abs_neg]
    exact ht
  have he : (∫ y, R y ∂σ) = U σ s-mp σ y0 s K := by
    have hsub := integral_sub (μ := σ) (f := fun y => -Real.log ‖s-y‖)
      (g := fun y => -Real.log ‖s-y0‖+(f y).re)
      hil.neg ((integrable_const _).add hif.re)
    have hadd := integral_add (μ := σ) (f := fun _ => -Real.log ‖s-y0‖)
      (g := fun y => (f y).re) (integrable_const _) hif.re
    have hre := integral_re hif
    simp only [RCLike.re_to_complex] at hre
    dsimp only [R]
    rw [hsub, hadd, integral_neg, integral_const, hre, hfi]
    simp only [RCLike.re_to_complex, smul_eq_mul, U, P, mp]
    ring
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [he, Real.norm_eq_abs] at hb'
  exact hb'.trans_eq (by dsimp only [mpErr, v]; ring)

#print axioms logPot_antitone_right
#print axioms logPot_antitone_right_closed
#print axioms multipole_point
#print axioms integrable_log_ball
#print axioms logPot_multipole
end CatalanCore.Li2.DecayCert
