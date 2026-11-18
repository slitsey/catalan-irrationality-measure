module
public import CatalanCore.Li2.DecayCert.Compile.Regular
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section
def ownCompileLegacy (d : QSegment) (p e : CQ) (lo hi : ℚ) (Jord terms : ℕ) : Option CompiledModel :=
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  if cqSq d.half ≠ 0 ∧ x.2=0 ∧ γ.2=0 ∧ lo ≤ hi ∧
      -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 ∧
      -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1 then
    let pown := d.ownPolyQ
    let rt := max |lo| |hi|
    let coeff := (List.range (Jord+1)).map (fun j : ℕ =>
      let q := (qShiftCoeff pown x γ j).1
      if j=0 then seAdd (seRat q)
        (seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))) else seRat q)
    some ⟨coeff,seRat ((List.range (pown.natDegree+1)).map (fun j : ℕ =>
      if Jord < j then |(qShiftCoeff pown x γ j).1| *rt^j else 0)).sum⟩
  else none

theorem ownCompile_branch_point_cross_direction_rejected (J terms : ℕ) :
    ownCompileLegacy ⟨(0,0),(1,0),[1]⟩ (1,0) (0,1) 0 0 J terms=none := by
  simp [ownCompileLegacy,cqDiv,cqMul,cqInv,cqSq,cqSub,cqAdd,cqNeg]

theorem ownCompile_branch_point_cross_direction_accepted (J terms : ℕ) :
    (ownCompile ⟨(0,0),(1,0),[1]⟩ (1,0) (0,1) 0 0 J terms).isSome=true := by
  simp [ownCompile,cqDiv,cqMul,cqInv,cqSq,cqSub,cqAdd,cqNeg]

theorem segment_singleton_own_model (d : SegmentData) (hpos : d.densityNonneg)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) (e : ℂ) :
    ModelsOn (fun u : ℝ => P d.ν (d.M+d.h*(x:ℂ)+e*(u:ℂ)))
      [d.c 0*(Real.log ‖d.h‖-Real.log 2)-
        ∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x/(k+1:ℕ)] 0 0 0 := by
  refine ⟨le_rfl,le_rfl,?_⟩
  intro u hu
  have hu0 : u=0 := le_antisymm hu.2 hu.1
  subst u
  simpa [evalModel,Finset.sum_range_succ] using
    (le_of_eq (show |P d.ν (d.M+d.h*(x:ℂ))-
      (d.c 0*(Real.log ‖d.h‖-Real.log 2)-
        ∑ k ∈ Finset.range d.N,d.c (k+1)*T (k+1) x/(k+1:ℕ))|=0 by
          rw [segPot_closed_own d hpos x hx,sub_self,abs_zero]))

noncomputable def QSegment.toSegment (d : QSegment) (hh : cqReal d.half ≠ 0) : SegmentData :=
  ⟨cqReal d.mid,cqReal d.half,hh,d.coeff.length-1,(fun k => (d.c k:ℝ)),by
    intro k hk
    simp [QSegment.c,List.getElem?_eq_none (by omega : d.coeff.length ≤ k)]⟩

theorem polynomial_eval_real_cast (p : ℚ[X]) (x : ℝ) :
    (p.map (Rat.castHom ℂ)).eval (x:ℂ)=(((p.map (Rat.castHom ℝ)).eval x:ℝ):ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add,Polynomial.eval_add,hp,hq,Complex.ofReal_add]
  | monomial n r =>
    simp only [Polynomial.map_monomial,Polynomial.eval_monomial,Rat.coe_castHom]
    push_cast
    rfl

theorem qOwnPoly_value (d : QSegment) (x : ℝ) :
    (d.ownPolyQ.map (Rat.castHom ℝ)).eval x=
      -(∑ k ∈ Finset.range (d.coeff.length-1),(d.c (k+1):ℝ)*T (k+1) x/(k+1:ℕ)) := by
  simp only [QSegment.ownPolyQ,Polynomial.map_neg,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.Chebyshev.map_T,Polynomial.eval_neg,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Rat.coe_castHom,T]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem QSegment.own_point_value (d : QSegment) (hh : cqReal d.half ≠ 0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    P d.measure (cqReal d.mid+cqReal d.half*(x:ℂ))=
      (d.ownPolyQ.map (Rat.castHom ℝ)).eval x+
        (d.c 0:ℝ)*(Real.log ‖cqReal d.half‖-Real.log 2) := by
  have hdpos : (d.toSegment hh).densityNonneg := hpos
  have he := segPot_closed_own (d.toSegment hh) hdpos x hx
  change P d.measure (cqReal d.mid+cqReal d.half*(x:ℂ))=
    (d.c 0:ℝ)*(Real.log ‖cqReal d.half‖-Real.log 2)-
      (∑ k ∈ Finset.range (d.coeff.length-1),(d.c (k+1):ℝ)*T (k+1) x/(k+1:ℕ)) at he
  rw [he,qOwnPoly_value]
  ring

theorem qShiftCoeff_zero_re (p : ℚ[X]) (x γ : CQ) :
    ((qShiftCoeff p x γ 0).1:ℝ)=((p.map (Rat.castHom ℂ)).eval (cqReal x)).re := by
  rw [← cqReal_re,qShiftCoeff_spec,Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp]
  simp

def ownScalarCoeff (d : QSegment) (x γ : CQ) (terms j : ℕ) : SE :=
  let q := (qShiftCoeff d.ownPolyQ x γ j).1
  if j=0 then seAdd (seRat q)
    (seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))) else seRat q

theorem ownCompile_singleton_shape (d : QSegment) (p e : CQ) (J terms : ℕ)
    (m : CompiledModel) (hc : ownCompile d p e 0 0 J terms=some m) :
    let x := cqDiv (cqSub p d.mid) d.half
    let γ := cqDiv e d.half
    cqSq d.half ≠ 0 ∧ x.2=0 ∧ (-1 ≤ x.1 ∧ x.1 ≤ 1) ∧
      m.coeff=(List.range (J+1)).map (ownScalarCoeff d x γ terms) ∧ m.error=seRat 0 := by
  dsimp only [ownCompile] at hc
  split_ifs at hc with hg
  have he := Option.some.inj hc
  cases he
  refine ⟨hg.1,hg.2.1,⟨?_,?_⟩,rfl,?_⟩
  · simpa only [mul_zero,add_zero] using hg.2.2.2.2.1
  · simpa only [mul_zero,add_zero] using hg.2.2.2.2.2.1
  · apply congrArg seRat
    rw [list_sum_map_range]
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with hJj
    · have hj0 : j ≠ 0 := by omega
      simp only [abs_zero,max_self,zero_pow hj0,mul_zero]
    · rfl

theorem evalModel_range_zero (f : ℕ → ℝ) (J : ℕ) :
    evalModel ((List.range (J+1)).map f) 0=f 0 := by
  rw [evalModel_map_range,Finset.sum_eq_single 0]
  · simp
  · intro n hn hne
    simp [zero_pow hne]
  · simp

theorem ownScalarCoeff_zero_value (d : QSegment) (x γ : CQ) (terms : ℕ) :
    (ownScalarCoeff d x γ terms 0).value=((qShiftCoeff d.ownPolyQ x γ 0).1:ℝ)+
      (d.c 0:ℝ)*(Real.log ‖cqReal d.half‖-Real.log 2) := by
  change (seAdd (seRat _) (seScale _ (seSub (seLogNorm terms d.half) (.log terms 2)))).value=_
  rw [seAdd_value,seRat_value,seScale_value,seSub_value,seLogNorm_value]
  rfl

theorem ownCompile_singleton_sound (d : QSegment) (p e : CQ) (J terms : ℕ)
    (m : CompiledModel)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : ownCompile d p e 0 0 J terms=some m) :
    ModelsOn (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) 0 0 m.error.value := by
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  rcases ownCompile_singleton_shape d p e J terms m hc with ⟨hh,hx2,hxi,hcoeff,herror⟩
  have hhalf : cqReal d.half ≠ 0 := by
    intro hz
    have hzero : (cqSq d.half:ℝ)=0 := by rw [cqSq_eq_norm_sq,hz,norm_zero]; norm_num
    exact hh (by exact_mod_cast hzero)
  have hx2x : x.2 = 0 := hx2
  have hxReal : cqReal x=(((x.1:ℝ):ℂ)) := by simp [cqReal,hx2x]
  have hxnorm : cqReal x=(cqReal p-cqReal d.mid)/cqReal d.half := by
    dsimp only [x]
    rw [cqReal_div,cqReal_sub]
  have hcenter : cqReal d.mid+cqReal d.half*((x.1:ℝ):ℂ)=cqReal p := by
    rw [← hxReal,hxnorm]
    field_simp [hhalf] <;> ring
  have hxiQ : (-1:ℚ) ≤ x.1 ∧ x.1 ≤ 1 := hxi
  have hxr : (x.1:ℝ) ∈ Icc (-1:ℝ) 1 := by
    constructor
    · exact_mod_cast hxiQ.1
    · exact_mod_cast hxiQ.2
  have hpoint := d.own_point_value hhalf hpos (x.1:ℝ) hxr
  rw [hcenter] at hpoint
  have heval : evalModel (m.coeff.map ScalarExpr.value) 0=P d.measure (cqReal p) := by
    rw [hcoeff,List.map_map,evalModel_range_zero]
    change (ownScalarCoeff d x γ terms 0).value=P d.measure (cqReal p)
    rw [ownScalarCoeff_zero_value,qShiftCoeff_zero_re,hxReal,polynomial_eval_real_cast,Complex.ofReal_re]
    exact hpoint.symm
  refine ⟨le_rfl,?_,?_⟩
  · rw [herror,seRat_value]
    norm_num
  · intro u hu
    have hu0 : u=0 := le_antisymm hu.2 hu.1
    subst u
    change |P d.measure (cqReal p+cqReal e*(0:ℂ))-evalModel (m.coeff.map ScalarExpr.value) 0| ≤ m.error.value
    rw [mul_zero,add_zero,heval,herror,seRat_value,sub_self,abs_zero]
    norm_num

theorem compileModel_sound_singleton_own (d : QSegment) (p e : CQ) (J terms : ℕ)
    (m : CompiledModel) (hpos : PositiveSources (.segment d p e))
    (hc : compileModel 0 0 (.segment d p e) (.segOwn J terms)=some m) :
    ModelsOn (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) 0 0 m.error.value :=
  ownCompile_singleton_sound d p e J terms m hpos hc

#print axioms ownCompile_branch_point_cross_direction_rejected
#print axioms ownCompile_branch_point_cross_direction_accepted
#print axioms segment_singleton_own_model
#print axioms polynomial_eval_real_cast
#print axioms qOwnPoly_value
#print axioms QSegment.own_point_value
#print axioms qShiftCoeff_zero_re
#print axioms ownCompile_singleton_shape
#print axioms evalModel_range_zero
#print axioms ownScalarCoeff_zero_value
#print axioms ownCompile_singleton_sound
#print axioms compileModel_sound_singleton_own
end
end CatalanCore.Li2.DecayCert
