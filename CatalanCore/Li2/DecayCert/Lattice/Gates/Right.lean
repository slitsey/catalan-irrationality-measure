module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Compiled
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Shape
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski

def rightGeometryCheck (d : LatticeInput) (c : RightCell) : Bool :=
  decide (d.Y≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧
    c.right=d.Y*(1+c.r)^2/(4*c.r))

theorem rightSeed_value (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (c : RightCell) (hc : rightGeometryCheck d c=true) :
    (segConstant c.terms d.first (1/c.r,0)).value=P d.first.measure ((c.right:ℝ):ℂ) := by
  have hg : d.Y≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧
      c.right=d.Y*(1+c.r)^2/(4*c.r) := of_decide_eq_true hc
  have hs := latticeShapeCheck_parts d hshape
  have hp := datum_source_data d.data dw hd d.first (lattice_first_mem d)
  have hr : (0:ℝ)<(c.r:ℝ) := by exact_mod_cast hg.2.2.1
  have hphiQ : (1:ℚ)<1/c.r := (one_lt_div hg.2.2.1).2 hg.2.2.2.1
  have hphiR : (1:ℝ)<((1/c.r:ℚ):ℝ) := by exact_mod_cast hphiQ
  have hphi : 1<‖cqReal (1/c.r,0)‖ := by
    have he : cqReal (1/c.r,0)=(((1/c.r:ℚ):ℝ):ℂ) := by simp [cqReal]
    rw [he,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ)<((1/c.r:ℚ):ℝ))]
    exact hphiR
  have heQ : d.Y/2+d.Y/2*((1/c.r+(1/c.r)⁻¹)/2)=c.right := by
    rw [hg.2.2.2.2]
    field_simp [hg.2.2.1.ne']
    <;>ring
  have hpt : cqReal d.first.mid+cqReal d.first.half*jJ (cqReal (1/c.r,0))=
      ((c.right:ℝ):ℂ) := by
    rw [hs.2.1,hs.2.2.1]
    simp only [cqReal,Rat.cast_zero,zero_mul,add_zero,jJ]
    have heC := congrArg (fun q : ℚ => (q:ℂ)) heQ
    push_cast at heC ⊢
    exact heC
  have he := segConstant_at_jJ c.terms d.first (1/c.r,0) hp.1 hphi hp.2.2
  rw [hpt] at he
  exact he.symm

theorem rightCellSource_majorizes (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hshape : latticeShapeCheck d=true) (c : RightCell)
    (hc : rightGeometryCheck d c=true) :
    ∀u∈Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ),
      W (z:ℝ) d.data.dual.σ (((c.left:ℝ)+u:ℝ):ℂ)≤(rightCellSource z d c).value u := by
  have hg : d.Y≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧
      c.right=d.Y*(1+c.r)^2/(4*c.r) := of_decide_eq_true hc
  have hs := latticeShapeCheck_parts d hshape
  have hp := datum_source_data d.data dw hd d.first (lattice_first_mem d)
  haveI := positive_source_finite d.first hp.2.2
  have hhalf : cqSq d.first.half≠0 := by
    rw [hs.2.2.1]
    dsimp only [cqSq]
    have hY := hs.1
    positivity
  have hno := segment_endpoint_atomless d.first hp.2.2 hhalf ((d.Y:ℝ):ℂ)
  have hi := d.data.dual.pointLogIntegrable ((d.Y:ℝ):ℂ)
  rw [lattice_sources d] at hi
  have hanti := logPot_antitone_right_closed d.first.measure (d.Y:ℝ)
    (lattice_first_support d hshape) hno (integrable_add_measure.mp hi).1
  have hseed := rightSeed_value d dw hd hshape c hc
  intro u hu
  have hleft : (d.Y:ℝ)≤(c.left:ℝ) := by exact_mod_cast hg.1
  have hright : (c.left:ℝ)+u≤(c.right:ℝ) := by
    have h := hu.2
    push_cast at h
    linarith
  have hx : (d.Y:ℝ)≤(c.left:ℝ)+u := by linarith [hu.1]
  have hm := hanti hx (hx.trans hright) hright
  have he := WExpr_value c.terms z hz d.data dw hd (c.left,0) (1,0) u
    (by
      have hY : (0:ℝ)<(d.Y:ℝ) := by exact_mod_cast hs.1
      simpa [cqReal] using (show (0:ℝ)≤(c.left:ℝ)+u by linarith))
    (by simp [cqReal])
  rw [d.source_eq] at he
  simp only [rightCellSource,WExpr,exprSum,CellExpr.value,List.map_cons,List.map_nil,
    List.foldl_cons,List.foldl_nil,ScalarExpr.value,Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat,
    zero_add,one_mul,cqReal,zero_mul,add_zero] at he ⊢
  rw [hseed]
  dsimp only [U] at hm he
  push_cast at hm he ⊢
  linarith only [he,hm]
#print axioms rightSeed_value
#print axioms rightCellSource_majorizes
end CatalanCore.Li2.DecayCert.LatticeGate
