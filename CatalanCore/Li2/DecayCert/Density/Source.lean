module
public import CatalanCore.Li2.DecayCert.Density.Regularity
public import CatalanCore.Lai.DecayInstance
public import CatalanCore.Decay.ComplexContour
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexEnergy
open CatalanCore.Decay.ComplexContour CatalanCore.Lai.DecayInstance
noncomputable section

theorem sourceDataCheck_parts (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) :
    (0 ≤ R ∧ ss.length=w.trees.length ∧ (ss.map (fun s => s.c 0)).sum=2) ∧
      ∀ s ∈ ss, ∃ t : BernsteinTree,
        (cqSq s.half ≠ 0 ∧ 0 < s.coeff.length ∧
          cqSq (cqAdd s.mid s.half) ≤ R^2 ∧ cqSq (cqSub s.mid s.half) ≤ R^2) ∧
        bernCheck s.density (-1) 1 t=true := by
  unfold sourceDataCheck at hc
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
  refine ⟨hc.1,?_⟩
  intro s hs
  rcases List.mem_iff_getElem.mp hs with ⟨j,hj,rfl⟩
  have hjc := List.all_eq_true.mp hc.2 j (List.mem_range.mpr hj)
  simp only [List.getElem?_eq_getElem hj] at hjc
  cases ht : w.trees[j]? with
  | none => simp [ht] at hjc
  | some t =>
    have hh : (cqSq ss[j].half ≠ 0 ∧ 0 < ss[j].coeff.length ∧
        cqSq (cqAdd ss[j].mid ss[j].half) ≤ R^2 ∧ cqSq (cqSub ss[j].mid ss[j].half) ≤ R^2) ∧
        bernCheck ss[j].density (-1) 1 t=true := by
      simpa only [ht,Bool.and_eq_true,decide_eq_true_eq] using hjc
    exact ⟨t,hh⟩

theorem density_real_eval (s : QSegment) (hlen : 0 < s.coeff.length) (x : ℝ) :
    (s.density.map (Rat.castHom ℝ)).eval x=
      CatalanCore.Zeta5.Potential.chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x := by
  have hlen' : s.coeff.length-1+1=s.coeff.length := by omega
  simp only [QSegment.density,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.Chebyshev.map_T,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Rat.coe_castHom,CatalanCore.Zeta5.Potential.chebF,hlen']

theorem sourceDataCheck_positive (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) :
    ∀ s ∈ ss, ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x := by
  intro s hs x hx
  rcases (sourceDataCheck_parts ss R w hc).2 s hs with ⟨t,hg,hb⟩
  have he := bernCheck_sound s.density (-1) 1 t hb x (by simpa only [Rat.cast_neg,Rat.cast_one] using hx)
  rwa [density_real_eval s hg.2.1 x] at he

theorem half_ne_of_cqSq_ne (q : CQ) (hq : cqSq q ≠ 0) : cqReal q ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [cqReal] at hr hi
  have hq1 : q.1=0 := hr
  have hq2 : q.2=0 := hi
  exact hq (by simp [cqSq,hq1,hq2])

theorem segment_ballMaj_exists (s : QSegment) (hh : cqReal s.half ≠ 0) :
    ∃ b A : ℝ, BallMajA s.measure b A (1/2) := by
  have hp := ballMajA_sig2 (M := cqReal s.mid) hh (fun k => (s.c k:ℝ)) (s.coeff.length-1)
  refine ⟨_,_,hp.b_pos,hp.A_nonneg,hp.α_pos,?_,?_⟩
  · exact segMeasure_compl (by linarith [norm_nonneg (cqReal s.mid),norm_nonneg (cqReal s.half)])
  · intro c r hr
    apply le_trans _ (hp.maj c r hr)
    rw [sig2,Measure.add_apply]
    exact le_add_of_nonneg_right (show (0:ENNReal) ≤ _ from bot_le)

theorem sources_ballMaj_exists (ss : List QSegment)
    (hh : ∀ s ∈ ss,cqReal s.half ≠ 0) :
    ∃ b A : ℝ, BallMajA (ss.map QSegment.measure).sum b A (1/2) := by
  induction ss with
  | nil => exact ⟨1,0,by simpa using BallMajA.zero (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (0:ℝ)<1/2)⟩
  | cons s ss ih =>
    rcases segment_ballMaj_exists s (hh s (List.mem_cons_self)) with ⟨b,A,hb⟩
    rcases ih (fun t ht => hh t (List.mem_cons_of_mem s ht)) with ⟨bb,AA,hbb⟩
    exact ⟨max b bb,A+AA,by simpa only [List.map_cons,List.sum_cons] using BallMajA.add hb hbb⟩

theorem positive_source_finite (s : QSegment)
    (hp : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) : IsFiniteMeasure s.measure :=
  isFiniteMeasure_segMeasure hp

theorem positive_source_mass (s : QSegment)
    (hp : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) : s.measure.real univ=(s.c 0:ℝ) := by
  have hc0 : 0 ≤ (s.c 0:ℝ) := by
    have hi : 0 ≤ ∫ θ : ℝ, CatalanCore.Zeta5.Potential.chebF
        (fun k => (s.c k:ℝ)) (s.coeff.length-1) (Real.cos θ) ∂CatalanCore.Zeta5.Potential.arc :=
      integral_nonneg (fun θ => hp _ (CatalanCore.Zeta5.Potential.cos_mem θ))
    rwa [CatalanCore.Zeta5.Potential.integral_chebF] at hi
  change (segMeasure (cqReal s.mid) (cqReal s.half) (fun k => (s.c k:ℝ)) (s.coeff.length-1) univ).toReal=_
  rw [segMeasure_univ hp,ENNReal.toReal_ofReal hc0]

theorem positive_sources_finite (ss : List QSegment)
    (hp : ∀ s ∈ ss,∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) : IsFiniteMeasure (ss.map QSegment.measure).sum := by
  induction ss with
  | nil => simpa using (inferInstance : IsFiniteMeasure (0:Measure ℂ))
  | cons s ss ih =>
    haveI := positive_source_finite s (hp s List.mem_cons_self)
    haveI := ih (fun t ht => hp t (List.mem_cons_of_mem s ht))
    simpa only [List.map_cons,List.sum_cons] using
      (inferInstance : IsFiniteMeasure (s.measure+(ss.map QSegment.measure).sum))

theorem positive_sources_mass (ss : List QSegment)
    (hp : ∀ s ∈ ss,∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) :
    (ss.map QSegment.measure).sum.real univ=(((ss.map (fun s => s.c 0)).sum:ℚ):ℝ) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    haveI := positive_source_finite s (hp s List.mem_cons_self)
    haveI := positive_sources_finite ss (fun t ht => hp t (List.mem_cons_of_mem s ht))
    simp only [List.map_cons,List.sum_cons,Rat.cast_add]
    rw [measureReal_add_apply (μ₁ := s.measure) (μ₂ := (ss.map QSegment.measure).sum) (s := univ)]
    rw [positive_source_mass s (hp s List.mem_cons_self),ih (fun t ht => hp t (List.mem_cons_of_mem s ht))]

theorem checkedDatum_exists (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) :
    ∃ d : CatalanCore.Li2.Uniform.DualDatum,d.σ=(ss.map QSegment.measure).sum := by
  have hp := sourceDataCheck_positive ss R w hc
  haveI := positive_sources_finite ss hp
  have hh : ∀ s ∈ ss,cqReal s.half ≠ 0 := by
    intro s hs
    rcases (sourceDataCheck_parts ss R w hc).2 s hs with ⟨t,hg,hb⟩
    exact half_ne_of_cqSq_ne s.half hg.1
  rcases sources_ballMaj_exists ss hh with ⟨b,A,hb⟩
  have hm : (ss.map QSegment.measure).sum.real univ=2 := by
    rw [positive_sources_mass ss hp,(sourceDataCheck_parts ss R w hc).1.2.2]
    norm_num
  exact datum_of_ballMajA_exists _ b A hb hm

theorem density_cqSq_norm (q : CQ) : (cqSq q:ℝ)=‖cqReal q‖^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply,cqReal_mk]
  simp [cqSq,pow_two]

theorem density_norm_le_of_sq (q : CQ) (R : ℚ) (hR : 0 ≤ R) (hq : cqSq q ≤ R^2) :
    ‖cqReal q‖ ≤ (R:ℝ) := by
  have hs : ‖cqReal q‖^2 ≤ (R:ℝ)^2 := by rw [← density_cqSq_norm]; exact_mod_cast hq
  have hr : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  nlinarith [norm_nonneg (cqReal q)]

theorem norm_segment_le_endpoints (M H : ℂ) (R : ℝ) (hm : ‖M-H‖ ≤ R) (hp : ‖M+H‖ ≤ R)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : ‖M+H*(x:ℂ)‖ ≤ R := by
  let a : ℝ := (1-x)/2
  let b : ℝ := (1+x)/2
  have ha : 0 ≤ a := by dsimp [a]; linarith [hx.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [hx.1]
  have he : M+H*(x:ℂ)=(a:ℂ)*(M-H)+(b:ℂ)*(M+H) := by dsimp [a,b]; push_cast; ring
  rw [he]
  calc
    _ ≤ ‖(a:ℂ)*(M-H)‖+‖(b:ℂ)*(M+H)‖ := norm_add_le _ _
    _ = a*‖M-H‖+b*‖M+H‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hm ha) (mul_le_mul_of_nonneg_left hp hb)
    _ = R := by dsimp [a,b]; ring

theorem segment_supported_endpoints (s : QSegment) (R : ℚ) (hR : 0 ≤ R)
    (hp : cqSq (cqAdd s.mid s.half) ≤ R^2) (hm : cqSq (cqSub s.mid s.half) ≤ R^2) :
    ∀ᵐ u ∂s.measure, ‖u‖ ≤ (R:ℝ) := by
  have hplus : ‖cqReal s.mid+cqReal s.half‖ ≤ (R:ℝ) := by
    simpa only [cqReal_add] using density_norm_le_of_sq (cqAdd s.mid s.half) R hR hp
  have hminus : ‖cqReal s.mid-cqReal s.half‖ ≤ (R:ℝ) := by
    simpa only [cqReal_sub] using density_norm_le_of_sq (cqSub s.mid s.half) R hR hm
  rw [← sourceParameter_map s]
  apply (ae_map_iff (by fun_prop)
    (isClosed_le continuous_norm continuous_const).measurableSet).mpr
  have hparam := measure_eq_zero_iff_ae_notMem.mp (sourceParameter_supported s)
  filter_upwards [hparam] with x hx
  have hxi : x ∈ Icc (-1:ℝ) 1 := by simpa only [Set.mem_compl_iff,not_not] using hx
  exact norm_segment_le_endpoints _ _ _ hminus hplus x hxi

theorem sources_supported (ss : List QSegment) (R : ℝ)
    (hs : ∀ s ∈ ss,∀ᵐ u ∂s.measure,‖u‖ ≤ R) :
    ∀ᵐ u ∂(ss.map QSegment.measure).sum,‖u‖ ≤ R := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons,ae_add_measure_iff]
    exact ⟨hs s List.mem_cons_self,ih (fun t ht => hs t (List.mem_cons_of_mem s ht))⟩

theorem sourceDataCheck_supported (ss : List QSegment) (R : ℚ) (w : DensityWitness)
    (hc : sourceDataCheck ss R w=true) :
    ∀ᵐ u ∂(ss.map QSegment.measure).sum,‖u‖ ≤ (R:ℝ) := by
  have hparts := sourceDataCheck_parts ss R w hc
  apply sources_supported
  intro s hs
  rcases hparts.2 s hs with ⟨t,hg,hb⟩
  exact segment_supported_endpoints s R hparts.1.1 hg.2.2.1 hg.2.2.2

#print axioms density_cqSq_norm
#print axioms density_norm_le_of_sq
#print axioms norm_segment_le_endpoints
#print axioms segment_supported_endpoints
#print axioms sources_supported
#print axioms sourceDataCheck_supported

#print axioms positive_source_finite
#print axioms positive_source_mass
#print axioms positive_sources_finite
#print axioms positive_sources_mass
#print axioms checkedDatum_exists

#print axioms sourceDataCheck_parts
#print axioms density_real_eval
#print axioms sourceDataCheck_positive
#print axioms half_ne_of_cqSq_ne
#print axioms segment_ballMaj_exists
#print axioms sources_ballMaj_exists
end
end CatalanCore.Li2.DecayCert
