module
public import CatalanCore.Li2.Decay.Weight
public import CatalanCore.Li2.Uniform.Datum
public import CatalanCore.Tools.CappedDual
public import CatalanCore.Tools.ExponentialSampling
public import CatalanCore.Li2.Uniform.Geometry
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay
theorem P_upper (d : DualDatum) (s : ℂ) (hs : 1 ≤ ‖s‖) :
    P d.σ s ≤ 2*Real.log (‖s‖+d.radius) := by
  have hh := CatalanCore.Tools.CappedDual.logPotential_upper d.σ s d.radius d.radius_nonneg
    d.bounded (by linarith [d.radius_nonneg]) (d.pointLogIntegrable s)
  simpa only [P,d.mass] using hh
theorem phi0_tail (s : ℂ) (hre : 0 ≤ s.re) (hs : 1 ≤ ‖s‖) :
    phi0 s ≤ -Real.log ‖s‖+3/‖s‖ := by
  have hs0 : 0 < ‖s‖ := by linarith
  have hi (B : ℝ) (hB : 0 ≤ B) :
      IntervalIntegrable (fun x : ℝ => Real.log ‖s+(x:ℂ)‖) volume 0 B := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    rw [uIcc_of_le hB] at hx
    exact (hs0.trans_le (norm_le_norm_add s hre x hx.1)).ne'
  have hlog : Real.log (‖s‖+1) ≤ Real.log ‖s‖+1/‖s‖ := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (‖s‖+1)/‖s‖ by positivity)
    rw [Real.log_div (by positivity) hs0.ne'] at hh
    have he : (‖s‖+1)/‖s‖-1=1/‖s‖ := by field_simp; ring
    rw [he] at hh
    linarith
  have hu := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (by norm_num)
    (hi 1 (by norm_num)) (intervalIntegrable_const (c := Real.log ‖s‖+1/‖s‖)) (by
      intro x hx
      apply (Real.log_le_log (hs0.trans_le (norm_le_norm_add s hre x hx.1)) _).trans hlog
      have hh := norm_add_le s (x:ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1] at hh
      linarith [hx.2])
  have hl := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const (c := Real.log ‖s‖)) (hi 4 (by norm_num)) (by
      intro x hx
      exact Real.log_le_log hs0 (norm_le_norm_add s hre x hx.1))
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hu hl
  change 3*(∫ x in (0:ℝ)..1, Real.log ‖s+(x:ℂ)‖)-
    (∫ x in (0:ℝ)..4, Real.log ‖s+(x:ℂ)‖) ≤ _
  simp only [div_eq_mul_inv,one_mul] at hu ⊢
  linarith

theorem field_tail_le (z : ℝ) (d : DualDatum) (s : ℂ)
    (hre : 0 ≤ s.re) (hs : 1 ≤ ‖s‖) :
    W z d.σ s ≤ -Real.log ‖s‖+3/‖s‖+4*Real.log (‖s‖+d.radius) +
      Real.log |z| *s.re-kappaRate z*|s.im| := by
  have hp := P_upper d s hs
  have hphi := phi0_tail s hre hs
  unfold W V U
  linarith
theorem phi0_global (s : ℂ) (hre : 0 ≤ s.re) :
    phi0 s ≤ 3*Real.log (1+‖s‖)+4 := by
  have hi (B : ℝ) (hB : 0 ≤ B) :
      IntervalIntegrable (fun t : ℝ => Real.log ‖s+(t:ℂ)‖) volume 0 B := by
    by_cases hs0 : s=0
    · simp only [hs0,zero_add,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
      exact intervalIntegral.intervalIntegrable_log'
    · have hs : 0 < ‖s‖ := norm_pos_iff.mpr hs0
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log (by fun_prop)
      intro t ht
      rw [uIcc_of_le hB] at ht
      exact (hs.trans_le (norm_le_norm_add s hre t ht.1)).ne'
  have hu := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (by norm_num)
    (hi 1 (by norm_num)) (intervalIntegrable_const (c := Real.log (1+‖s‖))) (by
      intro t ht
      have hnorm : ‖s+(t:ℂ)‖ ≤ 1+‖s‖ := by
        have hh := norm_add_le s (t:ℂ)
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
        linarith [ht.2]
      by_cases hzero : ‖s+(t:ℂ)‖=0
      · rw [hzero,Real.log_zero]
        exact Real.log_nonneg (by linarith [norm_nonneg s])
      · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hnorm)
  have hl := intervalIntegral.integral_mono_on_of_le_Ioo (a := (0:ℝ)) (b := 4) (by norm_num)
    intervalIntegral.intervalIntegrable_log' (hi 4 (by norm_num)) (by
      intro t ht
      apply Real.log_le_log ht.1
      calc
        t ≤ (s+(t:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
        _ ≤ |(s+(t:ℂ)).re| := le_abs_self _
        _ ≤ ‖s+(t:ℂ)‖ := Complex.abs_re_le_norm _)
  rw [integral_log_from_zero] at hl
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hu
  change 3*(∫ t in (0:ℝ)..1, Real.log ‖s+(t:ℂ)‖)-
    (∫ t in (0:ℝ)..4, Real.log ‖s+(t:ℂ)‖) ≤ _
  have hh : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem field_global (z : ℝ) (hz : ValidZ z) (d : DualDatum) :
    ∃ a : ℝ, 0 < a ∧ ∀ s : ℂ, 0 ≤ s.re →
      W z d.σ s ≤ 7*Real.log (1+‖s‖)+(4+4*Real.log (1+d.radius))-a*‖s‖ := by
  let a := min (-Real.log |z|) Real.pi
  have hL : Real.log |z| < 0 := Real.log_neg hz.1 hz.2
  have ha : 0 < a := lt_min (by linarith) Real.pi_pos
  refine ⟨a,ha,?_⟩
  intro s hre
  have hphi := phi0_global s hre
  have hrad := d.radius_nonneg
  have hp := CatalanCore.Tools.CappedDual.logPotential_upper d.σ s (d.radius+1)
    (by linarith) (by filter_upwards [d.bounded] with y hy; linarith)
    (by linarith [norm_nonneg s]) (d.pointLogIntegrable s)
  rw [d.mass] at hp
  have hlog : Real.log (‖s‖+(d.radius+1)) ≤ Real.log (1+‖s‖)+Real.log (1+d.radius) := by
    rw [← Real.log_mul (by positivity : (1+‖s‖) ≠ 0) (by positivity : (1+d.radius) ≠ 0)]
    apply Real.log_le_log (by positivity)
    nlinarith [mul_nonneg (norm_nonneg s) hrad]
  have haL : a ≤ -Real.log |z| := min_le_left _ _
  have haPi : a ≤ Real.pi := min_le_right _ _
  have hak : a ≤ kappaRate z := by
    unfold kappaRate
    split_ifs <;> linarith [Real.pi_pos]
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hre] at hn
  have hlin : Real.log |z| *s.re-kappaRate z*|s.im| ≤ -a*‖s‖ := by
    have h1 := mul_le_mul_of_nonneg_right haL hre
    have h2 := mul_le_mul_of_nonneg_right hak (abs_nonneg s.im)
    have h3 := mul_le_mul_of_nonneg_left hn ha.le
    linarith
  unfold W V U P
  linarith

theorem field_envelope (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ M a : ℝ, 0 < M ∧ 0 < a ∧ ∀ s : ℂ, 0 ≤ s.re →
      Real.exp (W z d.σ s-θ)*(1+‖s‖)^K ≤ M*Real.exp (-a*‖s‖) := by
  obtain ⟨a,ha,hfield⟩ := field_global z hz d
  obtain ⟨B,hB,hpow⟩ := CatalanCore.Decay.CurveFamily.pow_one_add_le_exp (K+7) (show 0 < a/2 by positivity)
  let M := (B+1)*Real.exp (4+4*Real.log (1+d.radius)-θ)
  refine ⟨M,a/2,by dsimp [M]; positivity,by positivity,?_⟩
  intro s hre
  have hb : 0 < 1+‖s‖ := by positivity
  have hexp : Real.exp (7*Real.log (1+‖s‖))=(1+‖s‖)^7 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hb] using Real.exp_nat_mul (Real.log (1+‖s‖)) 7
  have hh := Real.exp_le_exp.mpr (sub_le_sub_right (hfield s hre) θ)
  have he : 7*Real.log (1+‖s‖)+(4+4*Real.log (1+d.radius))-a*‖s‖-θ=
      (4+4*Real.log (1+d.radius)-θ)+7*Real.log (1+‖s‖)+(-a*‖s‖) := by ring
  rw [he,Real.exp_add,Real.exp_add,hexp] at hh
  calc
    _ ≤ (Real.exp (4+4*Real.log (1+d.radius)-θ)*(1+‖s‖)^7*Real.exp (-a*‖s‖))*(1+‖s‖)^K :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = Real.exp (4+4*Real.log (1+d.radius)-θ)*(1+‖s‖)^(K+7)*Real.exp (-a*‖s‖) := by rw [pow_add]; ring
    _ ≤ Real.exp (4+4*Real.log (1+d.radius)-θ)*(B*Real.exp ((a/2)*‖s‖))*Real.exp (-a*‖s‖) := by
      gcongr
      exact hpow ‖s‖ (norm_nonneg s)
    _ = B*Real.exp (4+4*Real.log (1+d.radius)-θ)*Real.exp (-(a/2)*‖s‖) := by
      rw [show -(a/2)*‖s‖=(a/2)*‖s‖+(-a*‖s‖) by ring,Real.exp_add]
      ring
    _ ≤ _ := by dsimp [M]; gcongr; linarith

theorem measurable_W (z : ℝ) (d : DualDatum) : Measurable (W z d.σ) := by
  have hphi (B : ℝ) (hB : 0 ≤ B) : Measurable (fun s : ℂ => ∫ t in (0:ℝ)..B, Real.log ‖s+(t:ℂ)‖) := by
    simp_rw [intervalIntegral.integral_of_le hB]
    have hh : Measurable (fun p : ℂ × ℝ => Real.log ‖p.1+(p.2:ℂ)‖) := by fun_prop
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hp : Measurable (P d.σ) := CatalanCore.Decay.CurveFamily.measurable_potC d.σ
  have hph : Measurable (phi0 : ℂ → ℝ) := (measurable_const.mul (hphi 1 (by norm_num))).sub (hphi 4 (by norm_num))
  unfold W V U
  fun_prop
theorem radial_piece (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (p : CatalanCore.Decay.CurveFamily.Piece) :
    Integrable (fun s : ℂ => M*Real.exp (-a*‖s‖)) (CatalanCore.Li2.Uniform.pieceArc p) :=
  CatalanCore.Tools.ExponentialSampling.radial_piece M a hM ha p

theorem radial_pieces (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (ps : List CatalanCore.Decay.CurveFamily.Piece) :
    Integrable (fun s : ℂ => M*Real.exp (-a*‖s‖)) (CatalanCore.Li2.Uniform.piecesArc ps) := by
  induction ps with
  | nil => simp [CatalanCore.Li2.Uniform.piecesArc]
  | cons p ps ih =>
    simp only [CatalanCore.Li2.Uniform.piecesArc,List.map_cons,List.sum_cons]
    exact (radial_piece M a hM ha p).add_measure ih

theorem radial_arc (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F) (s : ℤ) :
    Integrable (fun u : ℂ => M*Real.exp (-a*‖u‖)) (CatalanCore.Li2.Uniform.arcLength g s) := by
  cases g with
  | pure hp hl hf => simp [CatalanCore.Li2.Uniform.arcLength]
  | polygon p hp hl hf =>
    simp only [CatalanCore.Li2.Uniform.arcLength]
    apply ((radial_pieces M a hM ha _).add_measure (radial_pieces M a hM ha _)).add_measure
    split_ifs with hs
    · have hm : Measurable (fun u : ℂ => M*Real.exp (-a*‖u‖)) := by fun_prop
      apply (integrable_map_measure hm.aestronglyMeasurable Complex.measurable_ofReal.aemeasurable).2
      have hi : IntegrableOn (fun x : ℝ => M*Real.exp (-a*x)) (Ici p.cut) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).mpr
          ((integrableOn_exp_mul_Ioi (by linarith : -a < 0) p.cut).const_mul M)
      apply hi.congr
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx0 : 0 ≤ x := p.nonneg.trans hx
      simp only [Function.comp_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx0]
    · simp

theorem tail_arc_integrable (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    Integrable (fun s => Real.exp (W z d.σ s-θ)*(1+‖s‖)^K)
      (CatalanCore.Li2.Uniform.arcLength g (CatalanCore.Li2.Uniform.signOf z)) := by
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ K
  have hm : Measurable (fun s : ℂ => Real.exp (W z d.σ s-θ)*(1+‖s‖)^K) := by
    have hh := measurable_W z d
    fun_prop
  apply (radial_arc M a hM.le ha F g _).mono' hm.aestronglyMeasurable
  have hsupport := measure_eq_zero_iff_ae_notMem.mp
    (CatalanCore.Li2.Uniform.frame_arc_supported F g (CatalanCore.Li2.Uniform.signOf z))
  filter_upwards [hsupport] with s hs
  have hmem : s ∈ F.free (CatalanCore.Li2.Uniform.signOf z) := by simpa using hs
  have hre := (CatalanCore.Li2.Uniform.goodFrame_halfplane F g _).1 s hmem
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact hbound s hre
theorem geometric_sample (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    Summable (fun x : ℕ => M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))) ∧
      (∑' x : ℕ, M*Real.exp (-a*(((x+1:ℕ):ℝ)/n))) ≤ (M/a)*(n:ℝ) :=
  CatalanCore.Tools.ExponentialSampling.geometric_sample M a hM ha n hn

theorem tail_lattice_sum (z : ℝ) (hz : ValidZ z) (d : DualDatum) (θ : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (∑' x : ℕ, Real.exp (W z d.σ (((x+1:ℕ):ℂ)/n)-θ)*
        (1+((x+1:ℕ):ℝ)/n)^K) ≤ C*(n:ℝ) := by
  obtain ⟨M,a,hM,ha,hbound⟩ := field_envelope z hz d θ K
  refine ⟨M/a,by positivity,?_⟩
  intro n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnorm (x : ℕ) : ‖((x+1:ℕ):ℂ)/(n:ℂ)‖=((x+1:ℕ):ℝ)/(n:ℝ) := by
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
  have hpoint (x : ℕ) : Real.exp (W z d.σ (((x+1:ℕ):ℂ)/n)-θ)*
      (1+((x+1:ℕ):ℝ)/n)^K ≤ M*Real.exp (-a*(((x+1:ℕ):ℝ)/n)) := by
    have hh := hbound (((x+1:ℕ):ℂ)/(n:ℂ)) (by
      simp only [← Complex.ofReal_natCast,Complex.div_ofReal_re,Complex.ofReal_re]
      positivity)
    simpa only [hnorm] using hh
  obtain ⟨hs,hval⟩ := geometric_sample M a hM.le ha n hn
  have hg : Summable (fun x : ℕ => Real.exp (W z d.σ (((x+1:ℕ):ℂ)/n)-θ)*
      (1+((x+1:ℕ):ℝ)/n)^K) := Summable.of_nonneg_of_le (by intro x; positivity) hpoint hs
  exact (hg.tsum_le_tsum hpoint hs).trans hval

theorem tail_integrable (z : ℝ) (hz : ValidZ z)
    (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (d : CatalanCore.Li2.Uniform.DualDatum) (θ : ℝ) :
    (∀ K : ℕ, Integrable (fun s => Real.exp (W z d.σ s-θ)*(1+‖s‖)^K)
      (CatalanCore.Li2.Uniform.arcLength g (CatalanCore.Li2.Uniform.signOf z))) ∧
    (∀ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (∑' x : ℕ, Real.exp (W z d.σ (((x+1:ℕ):ℂ)/n)-θ)*
        (1+((x+1:ℕ):ℝ)/n)^K) ≤ C*(n:ℝ)) := by
  exact ⟨fun K => tail_arc_integrable z hz F g d θ K,fun K => tail_lattice_sum z hz d θ K⟩
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.field_tail_le
#print axioms CatalanCore.Li2.Decay.tail_integrable
