module
public import CatalanCore.Li2.DecayCert.FieldIntegral.Expressions
public import CatalanCore.Li2.DecayCert.FieldIntegral.LogBranch
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Polynomial Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem vintGeometry_half_ne (d : QSegment) (a : ℚ) (w : VSeed)
    (hg : vintGeometryCheck d a w=true) : cqReal d.half ≠ 0 := by
  have hh : cqSq d.half ≠ 0 := by
    intro hz
    simp only [vintGeometryCheck,hz,ite_true] at hg
    contradiction
  intro hz
  have he : (cqSq d.half:ℝ)=0 := by
    simp only [cqSq,Rat.cast_add,Rat.cast_pow]
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp [cqReal] at hr hi
    rw [hr,hi]
    norm_num
  exact hh (by exact_mod_cast he)

theorem checked_phase_bound (δ : ScalarExpr) (hcheck :
    (match δ.check,ScalarExpr.pi.check with
      | some b,some p => decide (max |b.1| |b.2| < p.1)
      | _,_ => false)=true) : |δ.value| < Real.pi := by
  cases hd : δ.check with
  | none => simp [hd] at hcheck
  | some b =>
    cases hp : ScalarExpr.pi.check with
    | none => simp [hd,hp] at hcheck
    | some p =>
      have hb := scalarCheck_sound δ b hd
      have hpi := scalarCheck_sound .pi p hp
      have hn : max |b.1| |b.2| < p.1 := of_decide_eq_true (by simpa only [hd,hp] using hcheck)
      have hnR : max |(b.1:ℝ)| |(b.2:ℝ)| < (p.1:ℝ) := by exact_mod_cast hn
      have hab : |δ.value| ≤ max |(b.1:ℝ)| |(b.2:ℝ)| := by
        apply abs_le.mpr
        constructor
        · have := le_max_left |(b.1:ℝ)| |(b.2:ℝ)|
          have := neg_abs_le (b.1:ℝ)
          linarith [hb.1]
        · have := le_max_right |(b.1:ℝ)| |(b.2:ℝ)|
          have := le_abs_self (b.2:ℝ)
          linarith [hb.2]
      exact hab.trans_lt (hnR.trans_le hpi.1)

theorem vintGeometry_generic_line (d : QSegment) (a : ℚ) (w : VSeed)
    (hg : vintGeometryCheck d a w=true)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : ¬ (d.mid.2=0 ∧ d.half.2=0)) :
    let η := cqReal (cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half))
    1 < jc η ∧ ∀ x ∈ Icc (-1:ℝ) 1,
      Complex.log (cqReal d.mid+(a:ℂ)+cqReal d.half*(x:ℂ)) =
        Complex.log (-cqReal d.half)+Complex.log (η-(x:ℂ))+2*Real.pi*Complex.I*(w.branch:ℂ) := by
  let β := cqAdd d.mid (a,0)
  let ηq := cqNeg (cqDiv β d.half)
  let δ := seSub (seSub (seSub (.arg w.terms β) (.arg w.terms (cqNeg d.half)))
    (.arg w.terms ηq)) (seScale (2*w.branch) .pi)
  have hh := vintGeometry_half_ne d a w hg
  have hsq : cqSq d.half ≠ 0 := by
    intro hz
    simp only [vintGeometryCheck,hz,ite_true] at hg
    contradiction
  rw [vintGeometryCheck,if_neg hsq,if_neg (not_or.mpr ⟨hnl,hnr⟩),if_neg hreal] at hg
  dsimp only at hg
  simp only [Bool.and_eq_true] at hg
  have hparts := hg
  have hd : 0 < slitDistSq ηq ∧
      0 ≤ (cqSub d.mid d.half).1+a ∧ 0 ≤ (cqAdd d.mid d.half).1+a ∧
      0 ≤ (cqSub d.mid d.half).2 ∧ 0 ≤ (cqAdd d.mid d.half).2 := of_decide_eq_true hparts.1
  have hoff := slitDistSq_pos_jc ηq hd.1
  have hδ : |δ.value| < Real.pi := checked_phase_bound δ hparts.2
  have hβ : cqReal β=cqReal d.mid+(a:ℂ) := by simp [β,cqReal,cqAdd] <;> ring
  have hfac : cqReal β=(-cqReal d.half)*cqReal ηq := by
    dsimp only [ηq]
    rw [cqReal_neg,cqReal_div]
    field_simp [hh] <;> ring
  have hphase : |Complex.arg (cqReal β)-Complex.arg (-cqReal d.half)-Complex.arg (cqReal ηq)-
      2*Real.pi*(w.branch:ℝ)| < Real.pi := by
    have hv : δ.value=Complex.arg (cqReal β)-Complex.arg (-cqReal d.half)-Complex.arg (cqReal ηq)-
        2*Real.pi*(w.branch:ℝ) := by
      dsimp only [δ,seSub,seAdd,seNeg,seScale,seMul,seRat,ScalarExpr.value]
      rw [cqReal_neg]
      push_cast
      ring
    rwa [hv] at hδ
  have hquad (y : ℝ) (hy : |y| ≤ 1) :
      0 ≤ (cqReal β+cqReal d.half*(y:ℂ)).re ∧ 0 ≤ (cqReal β+cqReal d.half*(y:ℂ)).im := by
    have hy' := abs_le.mp hy
    dsimp only [cqSub,cqAdd,cqNeg] at hd
    simp only [← sub_eq_add_neg] at hd
    have hloR : 0 ≤ ((d.mid.1:ℝ)-(d.half.1:ℝ))+(a:ℝ) := by exact_mod_cast hd.2.1
    have hhiR : 0 ≤ ((d.mid.1:ℝ)+(d.half.1:ℝ))+(a:ℝ) := by exact_mod_cast hd.2.2.1
    have hloI : 0 ≤ (d.mid.2:ℝ)-(d.half.2:ℝ) := by exact_mod_cast hd.2.2.2.1
    have hhiI : 0 ≤ (d.mid.2:ℝ)+(d.half.2:ℝ) := by exact_mod_cast hd.2.2.2.2
    have hre : (cqReal β+cqReal d.half*(y:ℂ)).re=(d.mid.1:ℝ)+(a:ℝ)+(d.half.1:ℝ)*y := by
      rw [hβ]
      simp [cqReal,Complex.mul_re]
    have him : (cqReal β+cqReal d.half*(y:ℂ)).im=(d.mid.2:ℝ)+(d.half.2:ℝ)*y := by
      rw [hβ]
      simp [cqReal,Complex.mul_im]
    rw [hre,him]
    constructor
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-y) hloR,mul_nonneg (by linarith : 0 ≤ 1+y) hhiR]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-y) hloI,mul_nonneg (by linarith : 0 ≤ 1+y) hhiI]
  refine ⟨hoff,?_⟩
  intro x hx
  have he := log_affine_branch (cqReal β) (cqReal d.half) (cqReal ηq) hh hoff hfac w.branch hquad hphase x hx
  rwa [hβ] at he

theorem weighted_tail_range (d : QSegment) (hh : cqReal d.half ≠ 0) (a : ℝ)
    {E : Type*} [AddCommMonoid E] (F : ℕ → ℂ → E) (hF : ∀ j, F j 0=0) :
    (∑ j ∈ Finset.range ((d.segmentData hh).N+1), F j (weightedCheb (d.segmentData hh) a (j+1))) =
      ∑ j ∈ Finset.range d.coeff.length, F j (weightedCheb (d.segmentData hh) a (j+1)) := by
  by_cases hz : d.coeff.length=0
  · have hnil : d.coeff=[] := List.eq_nil_of_length_eq_zero hz
    have hc (k : ℕ) : d.c k=0 := by simp [QSegment.c,hnil]
    have hw (k : ℕ) : weightedCheb (d.segmentData hh) a k=0 := by
      unfold weightedCheb
      dsimp only [QSegment.segmentData]
      simp only [hc,Rat.cast_zero,Complex.ofReal_zero,mul_zero,zero_div,add_zero]
      split_ifs <;> simp
    simp only [hw,hF,Finset.sum_const_zero]
  · have hlen : (d.segmentData hh).N+1=d.coeff.length := by
      change d.coeff.length-1+1=d.coeff.length
      omega
    rw [hlen]

theorem omegaArc_ae_Icc : ∀ᵐ (x : ℝ) ∂ωarc, x ∈ Icc (-1:ℝ) 1 := by
  apply (ae_map_iff Real.continuous_cos.aemeasurable measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall (fun θ => ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)

theorem cqReal_injective : Function.Injective cqReal := by
  intro x y h
  apply Prod.ext
  · have hh := congrArg Complex.re h
    simp only [cqReal_mk] at hh
    exact_mod_cast hh
  · have hh := congrArg Complex.im h
    simp only [cqReal_mk] at hh
    exact_mod_cast hh

theorem vintGeometry_real_off (d : QSegment) (a : ℚ) (w : VSeed)
    (hg : vintGeometryCheck d a w=true)
    (hnl : cqAdd d.mid (a,0) ≠ d.half) (hnr : cqAdd d.mid (a,0) ≠ cqNeg d.half)
    (hreal : d.mid.2=0 ∧ d.half.2=0) :
    let ηq := cqNeg (cqDiv (cqAdd d.mid (a,0)) d.half)
    1 < jc (cqReal ηq) ∧ 1 < |(cqReal ηq).re| := by
  let β := cqAdd d.mid (a,0)
  let ηq := cqNeg (cqDiv β d.half)
  have hh := vintGeometry_half_ne d a w hg
  have hsq : cqSq d.half ≠ 0 := by
    intro hz
    simp only [vintGeometryCheck,hz,ite_true] at hg
    contradiction
  rw [vintGeometryCheck,if_neg hsq,if_neg (not_or.mpr ⟨hnl,hnr⟩),if_pos hreal] at hg
  have hab : (1:ℚ) ≤ |ηq.1| := of_decide_eq_true hg
  have him : ηq.2=0 := by
    simp [ηq,β,cqNeg,cqDiv,cqMul,cqInv,cqSq,cqAdd,hreal.1,hreal.2]
  have hfac : cqReal β=(-cqReal d.half)*cqReal ηq := by
    dsimp only [ηq]
    rw [cqReal_neg,cqReal_div]
    field_simp [hh] <;> ring
  have hn1 : ηq.1 ≠ 1 := by
    intro he
    have hη : cqReal ηq=(1:ℂ) := by norm_num [cqReal,he,him]
    have hb : cqReal β=cqReal (cqNeg d.half) := by rw [hfac,hη,cqReal_neg,mul_one]
    exact hnr (cqReal_injective hb)
  have hnm1 : ηq.1 ≠ -1 := by
    intro he
    have hη : cqReal ηq=(-1:ℂ) := by norm_num [cqReal,he,him]
    have hb : cqReal β=cqReal d.half := by rw [hfac,hη]; ring
    exact hnl (cqReal_injective hb)
  have hstrict : (1:ℚ) < |ηq.1| := by
    by_cases hp : 0 ≤ ηq.1
    · rw [abs_of_nonneg hp] at hab ⊢
      exact lt_of_le_of_ne hab (Ne.symm hn1)
    · rw [abs_of_neg (lt_of_not_ge hp)] at hab ⊢
      have hm : ηq.1 < -1 := lt_of_le_of_ne (by linarith) hnm1
      linarith
  have hpos : 0 < slitDistSq ηq := by
    apply (slitDistSq_pos_iff ηq).mpr
    by_cases hp : 0 ≤ ηq.1
    · rw [abs_of_nonneg hp] at hstrict
      exact Or.inr (Or.inl hstrict)
    · rw [abs_of_neg (lt_of_not_ge hp)] at hstrict
      exact Or.inl (by linarith)
  refine ⟨slitDistSq_pos_jc ηq hpos,?_⟩
  have hre : (cqReal ηq).re=(ηq.1:ℝ) := by simp [cqReal]
  rw [hre]
  exact_mod_cast hstrict

#print axioms cqReal_injective
#print axioms vintGeometry_real_off

#print axioms weighted_tail_range
#print axioms omegaArc_ae_Icc

#print axioms vintGeometry_half_ne
#print axioms checked_phase_bound
#print axioms vintGeometry_generic_line
end
end CatalanCore.Li2.DecayCert
