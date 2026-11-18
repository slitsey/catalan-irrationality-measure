module
public import CatalanCore.Li2.DecayCert.Lattice.Chain
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Right
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem fullLatticeCell_penalty (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : PenaltyCell) (κ : ℚ)
    (hl : 0≤c.left) (hw : c.left≤c.right)
    (hc : cellUBF (fullLatticeCell z d c) c.witness=true) :
    (∫ x in (c.left:ℝ)..(c.right:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(κ:ℝ))) ≤
      (penaltyBoundQ c.scale c.witness (c.right-c.left) κ:ℝ) := by
  have hm := fullLatticeCell_source z hz d dw hd c hl hc
  exact penaltyCell_integral_bound c κ (sub_nonneg.mpr hw) _ (continuous_W_real _ _) hm.1 hm.2

theorem latticeAtomCell_penalty (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : PenaltyCell) (κ : ℚ)
    (hl : 1≤c.left) (hr : c.right≤4) (hw : c.left≤c.right)
    (hc : cellUBF (latticeAtomCell z d c) c.witness=true) :
    (∫ x in (c.left:ℝ)..(c.right:ℝ),pos (omega (z:ℝ) x-2*U d.data.dual.σ (-(x:ℂ))-(κ:ℝ))) ≤
      (penaltyBoundQ c.scale c.witness (c.right-c.left) κ:ℝ) := by
  have hm := latticeAtomCell_source z hz d dw hd c hl hr hc
  have hf : Continuous (fun x : ℝ => omega (z:ℝ) x-2*U d.data.dual.σ (-(x:ℂ))) := by
    convert continuous_A_real (z:ℝ) 0 d.data.dual using 1
    funext x
    simp only [A,sub_zero]
  exact penaltyCell_integral_bound c κ (sub_nonneg.mpr hw) _ hf hm.1 hm.2

theorem rightCell_penalty (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true) (c : RightCell) (κ : ℚ)
    (hc : rightCellCheck z d c=true) :
    (∫ x in (c.left:ℝ)..(c.right:ℝ),pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(κ:ℝ))) ≤
      (penaltyBoundQ c.scale c.witness (c.right-c.left) κ:ℝ) := by
  have hcheck := hc
  simp only [rightCellCheck,Bool.and_eq_true] at hcheck
  have hg : LatticeGate.rightGeometryCheck d c=true := hcheck.1
  have hgeom := of_decide_eq_true hcheck.1
  have hshape' := latticeShapeCheck_parts d hshape
  have hp := datum_source_data d.data dw hd d.second (lattice_second_mem d)
  have hP : Continuous (P d.second.measure) := by
    simpa only [QSegment.toSegment,SegmentData.ν,QSegment.measure] using
      (d.second.toSegment hp.1).continuous_P hp.2.2
  have hV : Continuous (fun x : ℝ => V (z:ℝ) (x:ℂ)) := by
    have hphi : Continuous (fun x : ℝ => phi0 (x:ℂ)) := by
      convert continuous_phi0_neg.comp continuous_neg using 1
      funext x
      simp only [Function.comp_apply,Complex.ofReal_neg,neg_neg]
    convert hphi.add ((continuous_const : Continuous (fun _ : ℝ => Real.log |(z:ℝ)|)).mul continuous_id) using 1
    funext x
    simp only [V,Complex.ofReal_re,Complex.ofReal_im,abs_zero,mul_zero,sub_zero,
      Pi.add_apply,Pi.mul_apply,id_eq]
  let g : ℝ → ℝ := fun u => V (z:ℝ) (((c.left:ℝ)+u:ℝ):ℂ)+
    2*(segConstant c.terms d.first (1/c.r,0)).value+2*P d.second.measure (((c.left:ℝ)+u:ℝ):ℂ)
  have hgc : Continuous g := (hV.comp (continuous_const.add continuous_id)).add continuous_const |>.add
    (continuous_const.mul (hP.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))))
  have he (u : ℝ) (hu : u∈Icc 0 ((c.right-c.left:ℚ):ℝ)) : (rightCellSource z d c).value u=g u := by
    have hleft : (0:ℝ)≤(c.left:ℝ)+u := by
      have hy : (0:ℝ)<(d.Y:ℝ) := by exact_mod_cast hshape'.1
      have hl : (d.Y:ℝ)≤(c.left:ℝ) := by exact_mod_cast hgeom.1
      linarith [hu.1]
    have hv := fieldExpr_value c.terms z (c.left,0) (1,0) u
      (by simpa [cqReal] using hleft) (by simp [cqReal])
    simp only [rightCellSource,CellExpr.value,g]
    rw [hv]
    simp [cqReal]
    ring
  have hcont : ContinuousOn (fun u => (rightCellSource z d c).value u) (Icc 0 ((c.right-c.left:ℚ):ℝ)) := by
    apply hgc.continuousOn.congr
    intro u hu
    exact he u hu
  have hpositive : PositiveSources (rightCellSource z d c) := by
    change PositiveSources (fieldExpr c.terms z (c.left,0) (1,0)) ∧ _
    refine ⟨?_,⟨trivial,hp.2.2⟩⟩
    unfold fieldExpr
    apply positiveSources_exprSum
    intro q hq
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> trivial
  have hm := cellUBF_model (rightCellInput z d c) c.witness hpositive hcheck.2
  have hb := cellUBF_spec (rightCellInput z d c) c.witness hpositive hcheck.2
  simp only [rightCellInput,Rat.cast_zero] at hm hb
  have hwidth : 0≤c.right-c.left := sub_nonneg.mpr hgeom.2.1.le
  have hi := penaltyBoundQ_sound c.scale c.witness (c.right-c.left) κ hwidth _ hcont hm hb
  have hRR : (0:ℝ)≤((c.right-c.left:ℚ):ℝ) := by exact_mod_cast hwidth
  have hposcont : ContinuousOn (fun u => pos ((rightCellSource z d c).value u-(κ:ℝ))) (Icc 0 ((c.right-c.left:ℚ):ℝ)) :=
    fun u hu => Filter.Tendsto.max ((hcont.sub continuous_const.continuousOn) u hu) tendsto_const_nhds
  have hmono : (∫ u in (0:ℝ)..((c.right-c.left:ℚ):ℝ),pos (W (z:ℝ) d.data.dual.σ (((c.left:ℝ)+u:ℝ):ℂ)-(κ:ℝ))) ≤
      ∫ u in (0:ℝ)..((c.right-c.left:ℚ):ℝ),pos ((rightCellSource z d c).value u-(κ:ℝ)) := by
    apply intervalIntegral.integral_mono_on hRR
      ((((continuous_W_real _ _).comp (continuous_const.add continuous_id)).sub continuous_const).max continuous_const |>.intervalIntegrable _ _)
      (hposcont.intervalIntegrable_of_Icc hRR)
    intro u hu
    exact max_le_max (sub_le_sub_right (LatticeGate.rightCellSource_majorizes z hz d dw hd hshape c hg u hu) _) le_rfl
  have heI := intervalIntegral.integral_comp_add_left (fun x : ℝ => pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(κ:ℝ))) (c.left:ℝ) (a:=0) (b:=((c.right-c.left:ℚ):ℝ))
  simp only [add_zero,Rat.cast_sub,add_sub_cancel] at heI
  simp only [Rat.cast_sub] at hmono hi
  rw [heI] at hmono
  exact hmono.trans hi
#print axioms fullLatticeCell_penalty
#print axioms latticeAtomCell_penalty
#print axioms rightCell_penalty
end
end CatalanCore.Li2.DecayCert
