module
public import CatalanCore.Li2.DecayCert.Series
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski

noncomputable def discMajorant (d : SegmentData) (ζ : ℂ) (dist fraction : ℝ) : ℝ :=
  let Z := ‖ζ‖+fraction*dist
  let Φ := Z+Real.sqrt (Z^2+1)
  |d.c 0| *(Real.log Φ+Real.log 2+Real.pi-Real.log (1-fraction))+
    ∑ k ∈ Finset.range d.N, |d.c (k+1)|/(k+1:ℕ)

theorem HasTaylorSeriesAt.iteratedDeriv {f : ℂ → ℂ} {b : ℕ → ℂ} {x : ℂ}
    (hb : HasTaylorSeriesAt f b x) (n : ℕ) :
    _root_.iteratedDeriv n f x=(n.factorial:ℂ)*b n := by
  induction n generalizing f b with
  | zero => simpa using hb.zero.symm
  | succ n ih =>
    rw [iteratedDeriv_succ',ih hb.deriv,Nat.factorial_succ]
    push_cast
    ring

theorem taylor_coeff_bound_sphere {f : ℂ → ℂ} {b : ℕ → ℂ} (hb : HasTaylorSeriesAt f b 0)
    (ρ M : ℝ) (hρ : 0 < ρ) (hf : DiffContOnCl ℂ f (Metric.ball 0 ρ))
    (hM : ∀ z ∈ Metric.sphere 0 ρ, ‖f z‖ ≤ M) (n : ℕ) : ‖b n‖ ≤ M/ρ^n := by
  have hr := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hf hM
  rw [hb.iteratedDeriv n,norm_mul] at hr
  have hh : (n.factorial:ℝ)*‖b n‖ ≤ (n.factorial:ℝ)*M/ρ^n := by simpa using hr
  have hfac : (0:ℝ)<(n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  apply (mul_le_mul_iff_right₀ hfac).mp
  calc
    _ ≤ (n.factorial:ℝ)*M/ρ^n := hh
    _ = _ := by ring

theorem taylor_coeff_bound_ball {f : ℂ → ℂ} {b : ℕ → ℂ} (hb : HasTaylorSeriesAt f b 0)
    (R M : ℝ) (hR : 0 < R) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hM : ∀ z ∈ Metric.ball 0 R, ‖f z‖ ≤ M) (n : ℕ) : ‖b n‖ ≤ M/R^n := by
  have hc : ContinuousAt (fun ρ : ℝ => M/ρ^n) R :=
    continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne')
  apply ge_of_tendsto (hc.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin R (Iio R) ≤ nhds R))
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Ioi_mem_nhds hR) : ∀ᶠ ρ : ℝ in nhdsWithin R (Iio R), 0 < ρ)] with ρ hρR hρ
  apply taylor_coeff_bound_sphere hb ρ M hρ
    (hf.diffContOnCl_ball (Metric.closedBall_subset_ball hρR))
  intro z hz
  exact hM z ((Metric.closedBall_subset_ball hρR) (Metric.sphere_subset_closedBall hz))

def sourceSlit : Set ℂ := Complex.ofReal '' Icc (-1:ℝ) 1

theorem infDist_slit_le_norm_jq (ζ : ℂ) (hs : 1 < jc ζ) :
    Metric.infDist ζ sourceSlit ≤ ‖jq ζ‖ := by
  have hone : (1:ℂ) ∈ sourceSlit := ⟨1,by constructor <;> norm_num,by simp⟩
  have hmone : (-1:ℂ) ∈ sourceSlit := ⟨-1,by constructor <;> norm_num,by simp⟩
  have h₁ : Metric.infDist ζ sourceSlit ≤ ‖ζ-1‖ := by
    simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x:=ζ) hone
  have h₂ : Metric.infDist ζ sourceSlit ≤ ‖ζ+1‖ := by
    simpa only [dist_eq_norm,sub_neg_eq_add] using Metric.infDist_le_dist_of_mem (x:=ζ) hmone
  have hq : ‖jq ζ‖^2=‖ζ-1‖*‖ζ+1‖ := by
    calc
      _ = ‖(jq ζ)^2‖ := (norm_pow _ _).symm
      _ = ‖ζ^2-1‖ := by rw [jq_sq hs]
      _ = ‖(ζ-1)*(ζ+1)‖ := by congr 1; ring
      _ = _ := norm_mul _ _
  have hd : 0 ≤ Metric.infDist ζ sourceSlit := Metric.infDist_nonneg
  have hp := mul_le_mul h₁ h₂ hd (norm_nonneg (ζ-1))
  nlinarith [norm_nonneg (jq ζ)]

theorem norm_jq_path_lower (ζ w : ℂ) (hw : 1 < jc w) :
    Metric.infDist ζ sourceSlit-‖w-ζ‖ ≤ ‖jq w‖ := by
  have hh := Metric.infDist_le_infDist_add_dist (x:=ζ) (y:=w) (s:=sourceSlit)
  have hq := infDist_slit_le_norm_jq w hw
  rw [dist_eq_norm,norm_sub_rev] at hh
  linarith
theorem HasTaylorSeriesAt.hasSum_ball {f : ℂ → ℂ} {b : ℕ → ℂ}
    (hb : HasTaylorSeriesAt f b 0) {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R)) {u : ℂ} (hu : ‖u‖ < R) :
    HasSum (fun n => b n*u^n) (f u) := by
  obtain ⟨ρ,hρu,hρR⟩ := exists_between hu
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg u) hρu
  lift ρ to NNReal using hρ.le
  have hp := (hf.mono (Metric.closedBall_subset_ball hρR)).hasFPowerSeriesOnBall hρ
  have he := hb.hasFPowerSeriesAt.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  rw [← he] at hp
  have hu' : u ∈ Metric.eball (0:ℂ) (ρ:ENNReal) := by
    rw [Metric.eball_coe]
    simpa only [Metric.mem_ball,dist_zero_right] using hρu
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,zero_add,mul_comm]
    using hp.hasSum hu'

theorem taylor_remainder_bound {f : ℂ → ℂ} {b : ℕ → ℂ}
    (hb : HasTaylorSeriesAt f b 0) (R rt M : ℝ) (hR : 0 < R)
    (hrt : 0 ≤ rt ∧ rt < R) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hM : ∀ z ∈ Metric.ball 0 R, ‖f z‖ ≤ M)
    (u : ℂ) (hu : ‖u‖ ≤ rt) (n : ℕ) :
    ‖f u-(∑ k ∈ Finset.range n,b k*u^k)‖ ≤ M*(rt/R)^n/(1-rt/R) := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simpa using hR))
  have hr : rt/R < 1 := (div_lt_one hR).mpr hrt.2
  have hcoeff : ∀ k, ‖b k*u^k‖ ≤ M*(rt/R)^k := by
    intro k
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (M/R^k)*rt^k := mul_le_mul (taylor_coeff_bound_ball hb R M hR hf hM k)
        (pow_le_pow_left₀ (norm_nonneg u) hu k) (pow_nonneg (norm_nonneg u) k)
        (div_nonneg hM0 (pow_nonneg hR.le k))
      _ = _ := by rw [div_pow]; ring
  have hh := norm_sub_le_of_geometric_bound_of_hasSum hr hcoeff
    (hb.hasSum_ball hf (hu.trans_lt hrt.2)) n
  rwa [norm_sub_rev] at hh

theorem branchLog_hasDerivAt (L : ℂ → ℂ) (ζ γ : ℂ) (R : ℝ)
    (hLan : AnalyticOnNhd ℂ L (Metric.ball 0 R))
    (hLzero : L 0=Complex.log (jphi ζ/2))
    (hbranch : ∀ u ∈ Metric.ball (0:ℂ) R,
      1 < jc (ζ+γ*u) ∧ Complex.exp (L u)=jphi (ζ+γ*u)/2)
    (u : ℂ) (hu : u ∈ Metric.ball 0 R) :
    HasDerivAt L (γ/jq (ζ+γ*u)) u := by
  classical
  let d : SegmentData := ⟨0,1,one_ne_zero,0,(fun n => if n=0 then 1 else 0),
    by intro k hk; simp [Nat.ne_of_gt hk]⟩
  have hL : IsDiscSegmentPrimitive d ζ γ R L := by
    refine ⟨L,hLan,hLzero,?_⟩
    intro v hv
    refine ⟨(hbranch v hv).1,(hbranch v hv).2,?_⟩
    simp [d]
  simpa [d,fpoly,rpoly,div_eq_mul_inv] using discPrimitive_hasDerivAt d ζ γ R L hL u hu

theorem integral_radial_log (dist a : ℝ) (hd : 0 < dist) (ha : 0 ≤ a) (had : a < dist) :
    (∫ t in (0:ℝ)..1, a/(dist-t*a)) = -Real.log (1-a/dist) := by
  have hpos (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < dist-t*a := by
    nlinarith [ht.2]
  have hB : ContinuousOn (fun t : ℝ => a/(dist-t*a)) (Icc (0:ℝ) 1) :=
    continuousOn_const.div (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
      (fun t ht => (hpos t ht).ne')
  have hBi : IntervalIntegrable (fun t : ℝ => a/(dist-t*a)) volume 0 1 :=
    hB.intervalIntegrable_of_Icc (by norm_num)
  have hD (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => -Real.log (dist-t*a)) (a/(dist-t*a)) t := by
    have hp := hpos t (by simpa using ht)
    convert! ((hasDerivAt_const t dist).sub ((hasDerivAt_id t).mul_const a)).log hp.ne' |>.neg using 1
    all_goals simp only [Pi.sub_apply,id_eq,one_mul,zero_sub,neg_div,neg_neg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hBi]
  have he : 1-a/dist=(dist-a)/dist := by field_simp
  rw [he,Real.log_div (sub_pos.mpr had).ne' hd.ne']
  simp only [one_mul,zero_mul,sub_zero]
  ring

theorem branchLog_drift (L : ℂ → ℂ) (ζ γ : ℂ) (R dist : ℝ)
    (hd : 0 < dist) (hLan : AnalyticOnNhd ℂ L (Metric.ball 0 R))
    (hLzero : L 0=Complex.log (jphi ζ/2))
    (hbranch : ∀ u ∈ Metric.ball (0:ℂ) R,
      1 < jc (ζ+γ*u) ∧ Complex.exp (L u)=jphi (ζ+γ*u)/2)
    (hdist : dist=Metric.infDist ζ sourceSlit)
    (u : ℂ) (hu : ‖u‖ < R) (had : ‖γ*u‖ < dist) :
    ‖L u-L 0‖ ≤ -Real.log (1-‖γ*u‖/dist) := by
  let a := ‖γ*u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hpos (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < dist-t*a := by
    nlinarith [ht.2]
  have hpath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (t:ℂ)*u ∈ Metric.ball (0:ℂ) R := by
    rw [Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg u) ht.2).trans_lt hu
  have hder (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => L ((t:ℂ)*u)) (γ/jq (ζ+γ*((t:ℂ)*u))*u) t := by
    simpa only [Function.comp_def,one_mul] using ((branchLog_hasDerivAt L ζ γ R hLan hLzero hbranch _ (hpath t ht)).comp
      (t:ℂ) (h:=fun z : ℂ => z*u) ((hasDerivAt_id (t:ℂ)).mul_const u)).comp_ofReal
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖γ/jq (ζ+γ*((t:ℂ)*u))*u‖ ≤ a/(dist-t*a) := by
    have hl := norm_jq_path_lower ζ (ζ+γ*((t:ℂ)*u)) (hbranch _ (hpath t ht)).1
    have he : ‖ζ+γ*((t:ℂ)*u)-ζ‖=t*a := by
      have hh : ζ+γ*((t:ℂ)*u)-ζ=(t:ℂ)*(γ*u) := by ring
      rw [hh,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    rw [← hdist,he] at hl
    calc
      _ = a/‖jq (ζ+γ*((t:ℂ)*u))‖ := by dsimp [a]; rw [norm_mul,norm_div,norm_mul]; ring
      _ ≤ _ := div_le_div_of_nonneg_left ha (hpos t ht) hl
  have hBi : IntervalIntegrable (fun t : ℝ => a/(dist-t*a)) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ => a/(dist-t*a)) (Icc (0:ℝ) 1) :=
      continuousOn_const.div
        (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
        (fun t ht => (hpos t ht).ne')
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  have hh := norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num : (0:ℝ)≤1)
    (HasDerivAt.continuousOn hder)
    (fun t ht => (hder t ⟨ht.1.le,ht.2.le⟩).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [(hder t ⟨ht.1.le,ht.2.le⟩).deriv]
      exact hbound t ⟨ht.1.le,ht.2.le⟩)) hBi
  simpa only [Complex.ofReal_one,one_mul,Complex.ofReal_zero,zero_mul,
    integral_radial_log dist a hd ha had] using hh

theorem norm_jphi_upper (ζ : ℂ) (hs : 1 < jc ζ) :
    ‖jphi ζ‖ ≤ ‖ζ‖+Real.sqrt (‖ζ‖^2+1) := by
  have hq : ‖jq ζ‖^2 ≤ ‖ζ‖^2+1 := by
    calc
      _ = ‖(jq ζ)^2‖ := (norm_pow _ _).symm
      _ = ‖ζ^2-1‖ := by rw [jq_sq hs]
      _ ≤ ‖ζ^2‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp
  have hroot : ‖jq ζ‖ ≤ Real.sqrt (‖ζ‖^2+1) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hq
  rw [jphi_eq_add_jq hs]
  exact (norm_add_le _ _).trans (add_le_add_right hroot _)

theorem norm_log_half_jphi (ζ : ℂ) (hs : 1 < jc ζ) :
    ‖Complex.log (jphi ζ/2)‖ ≤
      Real.log (‖ζ‖+Real.sqrt (‖ζ‖^2+1))+Real.log 2+Real.pi := by
  let Φ := ‖ζ‖+Real.sqrt (‖ζ‖^2+1)
  have hφ : 0 < ‖jphi ζ‖ := lt_trans (by norm_num) (jphi_spec hs).1
  have hΦ : 0 < Φ := hφ.trans_le (norm_jphi_upper ζ hs)
  have hlo : 0 ≤ Real.log ‖jphi ζ‖ := Real.log_nonneg (jphi_spec hs).1.le
  have hhi : Real.log ‖jphi ζ‖ ≤ Real.log Φ := Real.log_le_log hφ (norm_jphi_upper ζ hs)
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl : |Real.log ‖jphi ζ/2‖| ≤ Real.log Φ+Real.log 2 := by
    rw [norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,Real.log_div hφ.ne' (by norm_num)]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hlo,abs_of_nonneg htwo]; linarith)
  calc
    _ ≤ |(Complex.log (jphi ζ/2)).re|+|(Complex.log (jphi ζ/2)).im| := by
      simpa only [Complex.re_add_im] using norm_re_im_le
        (Complex.log (jphi ζ/2)).re (Complex.log (jphi ζ/2)).im
    _ ≤ _ := by rw [Complex.log_re,Complex.log_im]; exact add_le_add hl (Complex.abs_arg_le_pi _)

theorem discPrimitive_norm_bound (d : SegmentData) (ζ γ : ℂ) (hd : 1 < jc ζ)
    (dist R fraction : ℝ) (hfraction : 0 < fraction ∧ fraction < 1)
    (hdist : dist=Metric.infDist ζ sourceSlit) (hγ : γ ≠ 0)
    (hR : R=fraction*dist/‖γ‖) (hRpos : 0 < R)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G) :
    ∀ u ∈ Metric.ball (0:ℂ) R, ‖G u‖ ≤ discMajorant d ζ dist fraction := by
  classical
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hdistpos : 0 < dist := by
    have hh : 0 < fraction*dist := (div_pos_iff_of_pos_right hγpos).mp (hR ▸ hRpos)
    exact (mul_pos_iff_of_pos_left hfraction.1).mp hh
  let Z := ‖ζ‖+fraction*dist
  let Φ := Z+Real.sqrt (Z^2+1)
  have hZ : ‖ζ‖ ≤ Z := le_add_of_nonneg_right (mul_nonneg hfraction.1.le hdistpos.le)
  have hΦ : ‖ζ‖+Real.sqrt (‖ζ‖^2+1) ≤ Φ := by
    apply add_le_add hZ
    apply Real.sqrt_le_sqrt
    nlinarith [norm_nonneg ζ]
  have hΦpos : 0 < ‖ζ‖+Real.sqrt (‖ζ‖^2+1) := by positivity
  have hlog : Real.log (‖ζ‖+Real.sqrt (‖ζ‖^2+1)) ≤ Real.log Φ :=
    Real.log_le_log hΦpos hΦ
  rcases hG with ⟨L,hLan,hLzero,hbranch⟩
  intro u hu
  have hu' : ‖u‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hu
  have ha : ‖γ*u‖ < fraction*dist := by
    rw [norm_mul]
    calc
      _ < ‖γ‖*R := mul_lt_mul_of_pos_left hu' hγpos
      _ = _ := by rw [hR]; field_simp
  have had : ‖γ*u‖ < dist := ha.trans (by nlinarith [hfraction.2])
  have hlf : -Real.log (1-‖γ*u‖/dist) ≤ -Real.log (1-fraction) := by
    apply neg_le_neg
    apply Real.log_le_log (sub_pos.mpr hfraction.2)
    have hh : ‖γ*u‖/dist < fraction := (div_lt_iff₀ hdistpos).mpr (by nlinarith [ha])
    linarith
  have hL : ‖L u‖ ≤ Real.log Φ+Real.log 2+Real.pi-Real.log (1-fraction) := by
    have hdiff := branchLog_drift L ζ γ R dist hdistpos hLan hLzero
      (fun v hv => ⟨(hbranch v hv).1,(hbranch v hv).2.1⟩) hdist u hu' had
    have hzero := norm_log_half_jphi ζ hd
    rw [← hLzero] at hzero
    have htri : ‖L u‖ ≤ ‖L u-L 0‖+‖L 0‖ := norm_le_norm_sub_add _ _
    linarith
  have hterms : ‖∑ k ∈ Finset.range d.N,
      (d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)/(k+1:ℕ)‖ ≤
      ∑ k ∈ Finset.range d.N, |d.c (k+1)|/(k+1:ℕ) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    have hφ := (jphi_spec (hbranch u hu).1).1
    have hinv : ‖(jphi (ζ+γ*u))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (lt_trans (by norm_num) hφ)).mpr hφ.le
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have hn : ‖((k+1:ℕ):ℂ)‖=((k+1:ℕ):ℝ) := Complex.norm_natCast (k+1)
    rw [hn]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) hinv : ‖(jphi (ζ+γ*u))⁻¹‖^(k+1) ≤ 1) (abs_nonneg (d.c (k+1)))
  rw [(hbranch u hu).2.2]
  calc
    _ ≤ ‖(d.c 0:ℂ)*L u‖+‖∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)/(k+1:ℕ)‖ := norm_sub_le _ _
    _ ≤ |d.c 0| *(Real.log Φ+Real.log 2+Real.pi-Real.log (1-fraction))+
        ∑ k ∈ Finset.range d.N, |d.c (k+1)|/(k+1:ℕ) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hterms
    _ = _ := rfl

theorem cauchyDisc_cell (d : SegmentData) (ζ γ : ℂ) (hd : 1 < jc ζ)
    (dist R rt fraction : ℝ) (hfraction : 0 < fraction ∧ fraction < 1)
    (hdist : dist=Metric.infDist ζ (Complex.ofReal '' Icc (-1:ℝ) 1))
    (hγ : γ ≠ 0) (hR : R=fraction*dist/‖γ‖) (hrt : 0 ≤ rt ∧ rt < R)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G)
    (b : ℕ → ℂ) (hb : HasTaylorSeriesAt G b 0) (Jord : ℕ) :
  ∀ u : ℝ, |u| ≤ rt →
    |(G (u:ℂ)).re-(∑ n ∈ Finset.range (Jord+1), b n*(u:ℂ)^n).re| ≤
      discMajorant d ζ dist fraction*(rt/R)^(Jord+1)/(1-rt/R) := by
  have hRpos : 0 < R := hrt.1.trans_lt hrt.2
  have hf : DifferentiableOn ℂ G (Metric.ball 0 R) := by
    intro u hu
    exact (discPrimitive_hasDerivAt d ζ γ R G hG u hu).differentiableAt.differentiableWithinAt
  have hM := discPrimitive_norm_bound d ζ γ hd dist R fraction hfraction hdist hγ hR hRpos G hG
  intro u hu
  have hh := taylor_remainder_bound hb R rt (discMajorant d ζ dist fraction) hRpos hrt hf hM
    (u:ℂ) (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hu) (Jord+1)
  have hre := Complex.abs_re_le_norm (G (u:ℂ)-(∑ n ∈ Finset.range (Jord+1),b n*(u:ℂ)^n))
  rw [Complex.sub_re] at hre
  exact hre.trans hh

#print axioms cauchyDisc_cell
end CatalanCore.Li2.DecayCert
