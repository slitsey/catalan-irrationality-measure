module
public import CatalanCore.Li2.Uniform.Datum
public import CatalanCore.Tools.NeutralLogEnergy
@[expose] public section
/-! Uniform dual structure U0-U4, using the canonical datum closure and generic neutral logarithmic energy. -/
set_option Elab.async false
open MeasureTheory Set Filter Complex
open scoped Topology BigOperators
namespace CatalanCore.Li2.Uniform
private theorem measurable_phi0 : Measurable phi0 := by
  have hm : Measurable (fun p : ℂ × ℝ => Real.log ‖p.1+(p.2:ℂ)‖) := by fun_prop
  have h1 : Measurable (fun u : ℂ => ∫ x in (0:ℝ)..1, Real.log ‖u+(x:ℂ)‖) := by
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have h4 : Measurable (fun u : ℂ => ∫ x in (0:ℝ)..4, Real.log ‖u+(x:ℂ)‖) := by
    simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 4)]
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  exact (measurable_const.mul h1).sub h4
private theorem measurable_W (s : ℤ) (t : ℝ) (d : DualDatum) : Measurable (W s t d) := by
  have him : Measurable (fun u : ℂ => |u.im|) := by
    simp_rw [abs_eq_max_neg]
    exact Complex.measurable_im.max Complex.measurable_im.neg
  exact ((measurable_phi0.sub (measurable_const.mul Complex.measurable_re)).sub
    (measurable_const.mul him)).sub
    (measurable_const.mul (datum_continuous_pot d).measurable)
private theorem measurable_A (t r : ℝ) (d : DualDatum) : Measurable (A t r d) := by
  have hneg : Measurable (fun x : ℝ => -(x:ℂ)) := Complex.measurable_ofReal.neg
  exact (((measurable_phi0.comp hneg).add (measurable_const.mul measurable_id)).sub
    measurable_const).sub (measurable_const.mul ((datum_continuous_pot d).measurable.comp hneg))

theorem datum_depends_on_t (F : DualFrame) (s : ℤ) (z : ℚ) (t r : ℝ)
    (ht : Real.log (1/|(z:ℝ)|)=t) (d : DualDatum) (θ : ℝ) :
    Admissible F s (Real.log (1/|(z:ℝ)|)) d θ = Admissible F s t d θ ∧
    dual F s (Real.log (1/|(z:ℝ)|)) r d θ = dual F s t r d θ := by
  rw [ht]
  exact ⟨rfl,rfl⟩

theorem lattice_sign_blind (F : DualFrame) (hF : F.pure=true)
    (s0 s1 : ℤ) (d : DualDatum) (t r θ : ℝ) :
    Admissible F s0 t d θ = Admissible F s1 t d θ ∧
    CapIntegrable F s0 t r d θ = CapIntegrable F s1 t r d θ ∧
    dual F s0 t r d θ = dual F s1 t r d θ := by
  have hw (x : ℝ) : W s0 t d (x:ℂ)=W s1 t d (x:ℂ) := by simp [W]
  constructor
  · simp [Admissible,F.pure_free hF]
  constructor
  · simp only [CapIntegrable,hw]
  · simp only [dual,hw]

theorem dual_mono_rho (F : DualFrame) (s : ℤ) (d : DualDatum) (t θ r r' : ℝ)
    (hr : r ≤ r') (hc : CapIntegrable F s t r d θ) :
    CapIntegrable F s t r' d θ ∧ dual F s t r d θ ≤ dual F s t r' d θ := by
  have hp (x : ℝ) : max (A t r' d x-θ) 0 ≤ max (A t r d x-θ) 0 := by
    apply max_le_max _ le_rfl
    unfold A
    linarith
  have hiold : IntegrableOn (fun x => max (A t r d x-θ) 0) (Ioc (1:ℝ) 4) volume := hc.2.1
  have hinew : IntegrableOn (fun x => max (A t r' d x-θ) 0) (Ioc (1:ℝ) 4) volume := by
    apply hiold.mono' (((measurable_A t r' d).sub measurable_const).max measurable_const).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]; exact hp x
  have hnew : IntervalIntegrable (fun x => max (A t r' d x-θ) 0) volume 1 4 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 4)).mpr hinew
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 4) hnew hc.2 (fun x _ => hp x)
  refine ⟨⟨hc.1,hnew⟩,?_⟩
  unfold dual
  linarith

private noncomputable def crossEnergy (d0 d1 : DualDatum) : ℝ := ∫ u, pot d1.σ u ∂d0.σ
private theorem pot_integrable_cross (d0 d1 : DualDatum) : Integrable (pot d1.σ) d0.σ := by
  change Integrable (fun u : ℂ => ∫ y, -Real.log ‖u-y‖ ∂d1.σ) d0.σ
  simpa only [Pi.neg_apply] using (datum_cross_log_integrable d0 d1).neg.integral_prod_left
private theorem crossEnergy_eq_neg_pair (d0 d1 : DualDatum) :
    crossEnergy d0 d1 = -(∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(d0.σ.prod d1.σ)) := by
  rw [integral_prod _ (datum_cross_log_integrable d0 d1)]
  change (∫ u, (∫ y, -Real.log ‖u-y‖ ∂d1.σ) ∂d0.σ) = _
  simp_rw [integral_neg]
private theorem datum_neutral_energy (d0 d1 : DualDatum) :
    0 ≤ energy d0.σ-crossEnergy d0 d1-crossEnergy d1 d0+energy d1.σ := by
  let m : Bool → Measure ℂ := fun b => bif b then d0.σ else d1.σ
  haveI : ∀ b, IsFiniteMeasure (m b) := fun b => by
    cases b
    · simpa only [m,Bool.cond_false] using d1.finite
    · simpa only [m,Bool.cond_true] using d0.finite
  have h0 : ∀ᵐ z ∂d0.σ, ‖z‖ ≤ max d0.radius d1.radius := d0.bounded.mono fun z hz => hz.trans (le_max_left _ _)
  have h1 : ∀ᵐ z ∂d1.σ, ‖z‖ ≤ max d0.radius d1.radius := d1.bounded.mono fun z hz => hz.trans (le_max_right _ _)
  have key := CatalanCore.Tools.neutral_log_energy_nonneg (ι := Bool) (m := m)
    (s := fun b => bif b then 1 else -1) (R := max d0.radius d1.radius)
    (fun b => by cases b <;> simp only [m] <;> assumption)
    (by simp [Fintype.sum_bool,m,d0.mass,d1.mass])
    (fun b c => by cases b <;> cases c <;> simp only [m] <;> apply datum_cross_log_integrable)
    (fun b c => by cases b <;> cases c <;> simp only [m] <;> apply datum_cross_distinct)
  simp only [CatalanCore.Zeta5.Energy.energy,CatalanCore.Zeta5.Energy.pairInt,
    Fintype.sum_bool,m,cond_true,cond_false] at key
  have h00 := crossEnergy_eq_neg_pair d0 d0
  have h01 := crossEnergy_eq_neg_pair d0 d1
  have h10 := crossEnergy_eq_neg_pair d1 d0
  have h11 := crossEnergy_eq_neg_pair d1 d1
  change 0 ≤ crossEnergy d0 d0-crossEnergy d0 d1-crossEnergy d1 d0+crossEnergy d1 d1
  linarith
private theorem energy_mix_eq (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) :
    energy (mixDatum l hl d0 d1).σ =
      l^2*energy d0.σ + l*(1-l)*(crossEnergy d0 d1+crossEnergy d1 d0) + (1-l)^2*energy d1.σ := by
  let μ := ENNReal.ofReal l • d0.σ+ENNReal.ofReal (1-l) • d1.σ
  have hi (d : DualDatum) : Integrable (pot d.σ) μ :=
    integrable_add_measure.mpr ⟨(pot_integrable_cross d0 d).smul_measure ENNReal.ofReal_ne_top,
      (pot_integrable_cross d1 d).smul_measure ENNReal.ofReal_ne_top⟩
  have hx (d : DualDatum) : (∫ u, pot d.σ u ∂μ) = l*crossEnergy d0 d+(1-l)*crossEnergy d1 d := by
    rw [integral_add_measure ((pot_integrable_cross d0 d).smul_measure ENNReal.ofReal_ne_top)
      ((pot_integrable_cross d1 d).smul_measure ENNReal.ofReal_ne_top)]
    simp only [integral_smul_measure,ENNReal.toReal_ofReal hl.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hl.2),smul_eq_mul,crossEnergy]
  unfold energy
  rw [mixDatum_measure]
  simp_rw [pot_mix_measure l hl d0 d1]
  change (∫ u, l*pot d0.σ u+(1-l)*pot d1.σ u ∂μ) = _
  rw [integral_add ((hi d0).const_mul l) ((hi d1).const_mul (1-l)),integral_const_mul,integral_const_mul,hx,hx]
  change l*(l*crossEnergy d0 d0+(1-l)*crossEnergy d1 d0)+
    (1-l)*(l*crossEnergy d0 d1+(1-l)*crossEnergy d1 d1) = _
  change _ = l^2*crossEnergy d0 d0 + l*(1-l)*(crossEnergy d0 d1+crossEnergy d1 d0)+(1-l)^2*crossEnergy d1 d1
  ring
private theorem energy_mix_le (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) :
    energy (mixDatum l hl d0 d1).σ ≤ l*energy d0.σ+(1-l)*energy d1.σ := by
  rw [energy_mix_eq]
  have hh := mul_nonneg (mul_nonneg hl.1 (sub_nonneg.mpr hl.2)) (datum_neutral_energy d0 d1)
  nlinarith


private theorem max_mix_le (l : ℝ) (hl : l ∈ Icc 0 1) (x y : ℝ) :
    max (l*x+(1-l)*y) 0 ≤ l*max x 0+(1-l)*max y 0 := by
  apply max_le
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hl.1)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hl.2))
  · exact add_nonneg (mul_nonneg hl.1 (le_max_right _ _))
      (mul_nonneg (sub_nonneg.mpr hl.2) (le_max_right _ _))
private theorem W_mix_eq (s : ℤ) (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum)
    (t0 t1 : ℝ) (u : ℂ) :
    W s (l*t0+(1-l)*t1) (mixDatum l hl d0 d1) u = l*W s t0 d0 u+(1-l)*W s t1 d1 u := by
  unfold W
  rw [mixDatum_measure,pot_mix_measure l hl d0 d1]
  ring
private theorem A_mix_eq (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum)
    (t0 t1 r0 r1 x : ℝ) :
    A (l*t0+(1-l)*t1) (l*r0+(1-l)*r1) (mixDatum l hl d0 d1) x =
      l*A t0 r0 d0 x+(1-l)*A t1 r1 d1 x := by
  unfold A
  rw [mixDatum_measure,pot_mix_measure l hl d0 d1]
  ring

theorem dual_joint_concave (F : DualFrame) (s : ℤ)
    (d0 d1 : DualDatum) (t0 t1 r0 r1 θ0 θ1 l : ℝ) (hl : l ∈ Icc 0 1)
    (h0 : Admissible F s t0 d0 θ0) (h1 : Admissible F s t1 d1 θ1)
    (hcap0 : CapIntegrable F s t0 r0 d0 θ0) (hcap1 : CapIntegrable F s t1 r1 d1 θ1) :
    Admissible F s (l*t0+(1-l)*t1) (mixDatum l hl d0 d1) (l*θ0+(1-l)*θ1) ∧
    CapIntegrable F s (l*t0+(1-l)*t1) (l*r0+(1-l)*r1) (mixDatum l hl d0 d1) (l*θ0+(1-l)*θ1) ∧
    l*dual F s t0 r0 d0 θ0+(1-l)*dual F s t1 r1 d1 θ1 ≤
      dual F s (l*t0+(1-l)*t1) (l*r0+(1-l)*r1) (mixDatum l hl d0 d1) (l*θ0+(1-l)*θ1) := by
  let d := mixDatum l hl d0 d1
  let t := l*t0+(1-l)*t1
  let r := l*r0+(1-l)*r1
  let θ := l*θ0+(1-l)*θ1
  have hW (x : ℝ) : max (W s t d (x:ℂ)-θ) 0 ≤
      l*max (W s t0 d0 (x:ℂ)-θ0) 0+(1-l)*max (W s t1 d1 (x:ℂ)-θ1) 0 := by
    dsimp only [t,d,θ]
    rw [W_mix_eq]
    have he : l*W s t0 d0 (x:ℂ)+(1-l)*W s t1 d1 (x:ℂ)-(l*θ0+(1-l)*θ1) =
        l*(W s t0 d0 (x:ℂ)-θ0)+(1-l)*(W s t1 d1 (x:ℂ)-θ1) := by ring
    rw [he]
    exact max_mix_le l hl _ _
  have hA (x : ℝ) : max (A t r d x-θ) 0 ≤
      l*max (A t0 r0 d0 x-θ0) 0+(1-l)*max (A t1 r1 d1 x-θ1) 0 := by
    dsimp only [t,r,d,θ]
    rw [A_mix_eq]
    have he : l*A t0 r0 d0 x+(1-l)*A t1 r1 d1 x-(l*θ0+(1-l)*θ1) =
        l*(A t0 r0 d0 x-θ0)+(1-l)*(A t1 r1 d1 x-θ1) := by ring
    rw [he]
    exact max_mix_le l hl _ _
  have hlatmaj : IntegrableOn (fun x : ℝ => l*max (W s t0 d0 (x:ℂ)-θ0) 0+
      (1-l)*max (W s t1 d1 (x:ℂ)-θ1) 0) F.lattice volume :=
    (hcap0.1.const_mul l).add (hcap1.1.const_mul (1-l))
  have hlat : IntegrableOn (fun x : ℝ => max (W s t d (x:ℂ)-θ) 0) F.lattice volume := by
    apply hlatmaj.mono' ((((measurable_W s t d).comp Complex.measurable_ofReal).sub measurable_const).max measurable_const).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]; exact hW x
  have hatommaj := (hcap0.2.const_mul l).add (hcap1.2.const_mul (1-l))
  have hatomi : IntegrableOn (fun x : ℝ => max (A t r d x-θ) 0) (Ioc (1:ℝ) 4) volume := by
    apply hatommaj.1.mono' (((measurable_A t r d).sub measurable_const).max measurable_const).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]; exact hA x
  have hatom : IntervalIntegrable (fun x : ℝ => max (A t r d x-θ) 0) volume 1 4 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 4)).mpr hatomi
  have hlatbound := integral_mono_ae hlat hlatmaj (ae_of_all _ hW)
  rw [integral_add (hcap0.1.const_mul l) (hcap1.1.const_mul (1-l)),integral_const_mul,integral_const_mul] at hlatbound
  have hatombound := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 4) hatom hatommaj (fun x _ => hA x)
  rw [intervalIntegral.integral_add (hcap0.2.const_mul l) (hcap1.2.const_mul (1-l)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hatombound
  constructor
  · intro u hu
    rw [W_mix_eq]
    exact add_le_add (mul_le_mul_of_nonneg_left (h0 u hu) hl.1)
      (mul_le_mul_of_nonneg_left (h1 u hu) (sub_nonneg.mpr hl.2))
  refine ⟨⟨hlat,hatom⟩,?_⟩
  have henergy := energy_mix_le l hl d0 d1
  change l*dual F s t0 r0 d0 θ0+(1-l)*dual F s t1 r1 d1 θ1 ≤ dual F s t r d θ
  unfold dual
  dsimp only [θ] at *
  nlinarith


private theorem triangle_profile (m : ℝ) (hm : 0 ≤ m) :
    IntegrableOn (fun x : ℝ => max (m-x) 0) (Ici 0) volume ∧
      (∫ x in Ici (0:ℝ), max (m-x) 0) = m^2/2 := by
  have hc : IntegrableOn (fun x : ℝ => max (m-x) 0) (Icc 0 m) volume :=
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hz : IntegrableOn (fun x : ℝ => max (m-x) 0) (Ioi m) volume := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi m) volume).congr_fun _ measurableSet_Ioi
    intro x hx
    change 0 = max (m-x) 0
    change m<x at hx
    rw [max_eq_right (by linarith : m-x ≤ 0)]
  have hset : Icc (0:ℝ) m ∪ Ioi m = Ici 0 := by
    ext x
    simp only [Set.mem_union,mem_Icc,mem_Ioi,mem_Ici]
    constructor
    · rintro (⟨hx,hx'⟩|hx) <;> linarith
    · intro hx
      by_cases hxm : x ≤ m
      · exact Or.inl ⟨hx,hxm⟩
      · exact Or.inr (lt_of_not_ge hxm)
  have hi : IntegrableOn (fun x : ℝ => max (m-x) 0) (Ici 0) volume := by
    rw [← hset]
    exact integrableOn_union.mpr ⟨hc,hz⟩
  refine ⟨hi,?_⟩
  have hdisj : Disjoint (Icc (0:ℝ) m) (Ioi m) := disjoint_left.mpr (fun x hx hy => not_lt_of_ge hx.2 hy)
  rw [← hset,setIntegral_union hdisj measurableSet_Ioi hc hz]
  have hzero : (∫ x in Ioi m, max (m-x) 0) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change m<x at hx
    simp only [max_eq_right (by linarith : m-x ≤ 0),Pi.zero_apply]
  rw [hzero,add_zero]
  have he : (∫ x in Icc (0:ℝ) m, max (m-x) 0) = ∫ x in Icc (0:ℝ) m, m-x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact max_eq_left (sub_nonneg.mpr hx.2)
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hm,
    intervalIntegral.integral_sub (f := fun _ : ℝ => m) (g := fun x : ℝ => x) (intervalIntegrable_const (c := m)) (continuous_id.intervalIntegrable 0 m),
    intervalIntegral.integral_const,integral_id]
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),smul_eq_mul]
  ring

private theorem lattice_triangle_bound (F : DualFrame) (m : ℝ) (hm : 0 ≤ m) :
    IntegrableOn (fun x : ℝ => max (m-x) 0) F.lattice volume ∧
      (∫ x in F.lattice, max (m-x) 0) ≤ m^2/2 := by
  have ht := triangle_profile m hm
  have hsub : F.lattice ⊆ Ici 0 := F.lattice_mem
  refine ⟨ht.1.mono_set hsub,?_⟩
  have hh := setIntegral_mono_set (s := F.lattice) ht.1 (ae_of_all _ fun x => le_max_right (m-x) 0)
    (ae_of_all _ fun x => hsub (a := x))
  exact hh.trans_eq ht.2


theorem dual_transport (F : DualFrame) (s : ℤ) (d : DualDatum) (t r θ m Δ : ℝ)
    (hm : m ∈ Icc 0 1) (hΔ : 0 ≤ Δ) (hfree : ∀ u ∈ F.free s, m ≤ u.re)
    (hadm : Admissible F s t d θ) (hcap : CapIntegrable F s t r d θ) :
    Admissible F s (t+Δ) d (θ-m*Δ) ∧
    CapIntegrable F s (t+Δ) (r+(4+m)*Δ) d (θ-m*Δ) ∧
    dual F s t r d θ+(2*m-m^2)*Δ ≤ dual F s (t+Δ) (r+(4+m)*Δ) d (θ-m*Δ) := by
  have hw (u : ℂ) : W s (t+Δ) d u-(θ-m*Δ) = W s t d u-θ+Δ*(m-u.re) := by
    unfold W
    ring
  have ha (x : ℝ) : A (t+Δ) (r+(4+m)*Δ) d x-(θ-m*Δ) = A t r d x-θ+Δ*(x-4) := by
    unfold A
    ring
  have hlatpoint (x : ℝ) : max (W s (t+Δ) d (x:ℂ)-(θ-m*Δ)) 0 ≤
      max (W s t d (x:ℂ)-θ) 0+Δ*max (m-x) 0 := by
    rw [hw,Complex.ofReal_re]
    apply max_le
    · exact add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_left (le_max_left _ _) hΔ)
    · exact add_nonneg (le_max_right _ _) (mul_nonneg hΔ (le_max_right _ _))
  have hatompoint (x : ℝ) (hx : x ≤ 4) :
      max (A (t+Δ) (r+(4+m)*Δ) d x-(θ-m*Δ)) 0 ≤ max (A t r d x-θ) 0 := by
    rw [ha]
    apply max_le_max _ le_rfl
    have hh := mul_nonpos_of_nonneg_of_nonpos hΔ (sub_nonpos.mpr hx)
    linarith
  have htri := lattice_triangle_bound F m hm.1
  have hlatmaj : IntegrableOn (fun x : ℝ => max (W s t d (x:ℂ)-θ) 0+Δ*max (m-x) 0) F.lattice volume :=
    hcap.1.add (htri.1.const_mul Δ)
  have hlat : IntegrableOn (fun x : ℝ => max (W s (t+Δ) d (x:ℂ)-(θ-m*Δ)) 0) F.lattice volume := by
    apply hlatmaj.mono' ((((measurable_W s (t+Δ) d).comp Complex.measurable_ofReal).sub measurable_const).max measurable_const).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]; exact hlatpoint x
  have hatomi : IntegrableOn (fun x : ℝ => max (A (t+Δ) (r+(4+m)*Δ) d x-(θ-m*Δ)) 0) (Ioc (1:ℝ) 4) volume := by
    apply hcap.2.1.mono' (((measurable_A (t+Δ) (r+(4+m)*Δ) d).sub measurable_const).max measurable_const).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact hatompoint x hx.2
  have hatom : IntervalIntegrable (fun x : ℝ => max (A (t+Δ) (r+(4+m)*Δ) d x-(θ-m*Δ)) 0) volume 1 4 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 4)).mpr hatomi
  have hlatbound := integral_mono_ae hlat hlatmaj (ae_of_all _ hlatpoint)
  rw [integral_add hcap.1 (htri.1.const_mul Δ),integral_const_mul] at hlatbound
  have htribound := mul_le_mul_of_nonneg_left htri.2 hΔ
  have hatombound := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ) ≤ 4) hatom hcap.2
    (fun x hx => hatompoint x hx.2)
  constructor
  · intro u hu
    have h0 := hadm u hu
    have h1 := mul_nonpos_of_nonneg_of_nonpos hΔ (sub_nonpos.mpr (hfree u hu))
    have he := hw u
    linarith
  refine ⟨⟨hlat,hatom⟩,?_⟩
  unfold dual
  nlinarith

end CatalanCore.Li2.Uniform
#print axioms CatalanCore.Li2.Uniform.datum_depends_on_t
#print axioms CatalanCore.Li2.Uniform.lattice_sign_blind
#print axioms CatalanCore.Li2.Uniform.dual_mono_rho

#print axioms CatalanCore.Li2.Uniform.energy_mix_le

#print axioms CatalanCore.Li2.Uniform.dual_joint_concave

#print axioms CatalanCore.Li2.Uniform.lattice_triangle_bound

#print axioms CatalanCore.Li2.Uniform.dual_transport
