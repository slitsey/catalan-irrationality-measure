module
public import CatalanCore.Li2.DecayCert.Lattice.Penalty
public import CatalanCore.Li2.DecayCert.Lattice.Shape
public import CatalanCore.Li2.Decay.Caps
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem WExpr_positive (terms : ℕ) (z : ℚ) (d : SegmentDatum) (dw : DensityWitness)
    (hd : datumCheck d dw=true) (p e : CQ) : PositiveSources (WExpr terms z d.segments p e) := by
  change PositiveSources (fieldExpr terms z p e) ∧ _
  refine ⟨?_,positiveSources_segmentSum d.segments p e (datumCheck_positive d dw hd).1⟩
  unfold fieldExpr
  apply positiveSources_exprSum
  intro q hq
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> trivial

theorem penaltyCell_parameter (c : PenaltyCell) (L U : ℚ)
    (hL : L ≤ c.left) (hU : c.right ≤ U) (u : ℝ)
    (hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ)) :
    (c.start:ℝ)+(c.dir:ℝ)*u ∈ Icc (L:ℝ) (U:ℝ) := by
  have hl : (L:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hL
  have hr : (c.right:ℝ) ≤ (U:ℝ) := by exact_mod_cast hU
  have huR : u ≤ (c.right:ℝ)-(c.left:ℝ) := by simpa only [Rat.cast_sub] using hu.2
  cases hb : c.backwards <;> simp only [PenaltyCell.start,PenaltyCell.dir,hb,Bool.false_eq_true,
    ite_false,ite_true,Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] <;>
      constructor <;> linarith [hu.1]

theorem penaltyCell_cq_point (c : PenaltyCell) (u : ℝ) :
    cqReal (c.start,0)+cqReal (c.dir,0)*(u:ℂ)=(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ) := by
  simp [cqReal] <;> push_cast <;> ring

def penaltyLineCell (c : PenaltyCell) (hw : 0 ≤ c.right-c.left) : LineCell where
  start := c.start
  len := c.right-c.left
  dir := c.dir
  a := 0
  b := 0
  len_nonneg := hw
  direction := by cases hb : c.backwards <;> simp [PenaltyCell.dir,hb]

theorem penaltyLineCell_support (c : PenaltyCell) (hw : 0 ≤ c.right-c.left) :
    (penaltyLineCell c hw).support=Icc (c.left:ℝ) (c.right:ℝ) := by
  cases hb : c.backwards
  · rw [LineCell.support_forward _ (by simp [penaltyLineCell,PenaltyCell.dir,hb])]
    simp only [penaltyLineCell,PenaltyCell.start,hb,Bool.false_eq_true,ite_false,Rat.cast_sub]
    congr 2 <;> ring
  · rw [LineCell.support_backward _ (by simp [penaltyLineCell,PenaltyCell.dir,hb])]
    simp only [penaltyLineCell,PenaltyCell.start,hb,ite_true,Rat.cast_sub]
    congr 2 <;> ring

theorem penaltyCell_integral_bound (c : PenaltyCell) (κ : ℚ) (hw : 0 ≤ c.right-c.left)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hm : ModelsOn (fun u => f ((c.start:ℝ)+(c.dir:ℝ)*u))
      ((gridCoeffs c.scale c.witness).map (fun q : ℚ => (q:ℝ))) 0 ((c.right-c.left:ℚ):ℝ) c.witness.remainder)
    (hb : ∀ u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ),f ((c.start:ℝ)+(c.dir:ℝ)*u) ∈
      Icc (c.witness.lb:ℝ) (c.witness.ub:ℝ)) :
    (∫ x in (c.left:ℝ)..(c.right:ℝ),pos (f x-(κ:ℝ))) ≤
      (penaltyBoundQ c.scale c.witness (c.right-c.left) κ:ℝ) := by
  have hwidth : (c.left:ℝ) ≤ (c.right:ℝ) := by exact_mod_cast sub_nonneg.mp hw
  have hp := penaltyBoundQ_sound c.scale c.witness (c.right-c.left) κ hw
    (fun u => f ((c.start:ℝ)+(c.dir:ℝ)*u)) ((hf.comp (by fun_prop)).continuousOn) hm hb
  have he := (penaltyLineCell c hw).integral_support (fun x => pos (f x-(κ:ℝ)))
  rw [penaltyLineCell_support] at he
  rw [intervalIntegral.integral_of_le hwidth,← integral_Icc_eq_integral_Ioc,he]
  exact hp

theorem fullLatticeCell_source (z : ℚ) (hz : z ≠ 0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : PenaltyCell) (hl : 0 ≤ c.left)
    (hc : cellUBF (fullLatticeCell z d c) c.witness=true) :
    ModelsOn (fun u => W (z:ℝ) d.data.dual.σ (((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ))
      ((gridCoeffs c.scale c.witness).map (fun q : ℚ => (q:ℝ))) 0 ((c.right-c.left:ℚ):ℝ) c.witness.remainder ∧
    ∀ u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ),W (z:ℝ) d.data.dual.σ
      (((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ) ∈ Icc (c.witness.lb:ℝ) (c.witness.ub:ℝ) := by
  have hp := WExpr_positive c.terms z d.data dw hd (c.start,0) (c.dir,0)
  have hm := cellUBF_model (fullLatticeCell z d c) c.witness hp hc
  have hb := cellUBF_spec (fullLatticeCell z d c) c.witness hp hc
  have he (u : ℝ) (hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ)) :
      (fullLatticeCell z d c).expr.value u=W (z:ℝ) d.data.dual.σ
        (((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ) := by
    change (WExpr c.terms z d.data.segments (c.start,0) (c.dir,0)).value u=_
    rw [WExpr_value c.terms z hz d.data dw hd _ _ u,penaltyCell_cq_point]
    · rw [penaltyCell_cq_point,Complex.ofReal_re]
      simpa only [Rat.cast_zero] using (penaltyCell_parameter c 0 c.right hl le_rfl u hu).1
    · rw [penaltyCell_cq_point,Complex.ofReal_im]
  simp only [fullLatticeCell,Rat.cast_zero] at hm hb
  refine ⟨⟨hm.1,hm.2.1,?_⟩,?_⟩
  · intro u hu
    dsimp only
    rw [← he u hu]
    exact hm.2.2 u hu
  · intro u hu
    rw [← he u hu]
    exact hb u hu

theorem latticeAtomCell_source (z : ℚ) (hz : z ≠ 0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : PenaltyCell) (hl : 1 ≤ c.left) (hr : c.right ≤ 4)
    (hc : cellUBF (latticeAtomCell z d c) c.witness=true) :
    ModelsOn (fun u => omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-
      2*U d.data.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)))
      ((gridCoeffs c.scale c.witness).map (fun q : ℚ => (q:ℝ))) 0 ((c.right-c.left:ℚ):ℝ) c.witness.remainder ∧
    ∀ u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ),omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-
      2*U d.data.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)) ∈ Icc (c.witness.lb:ℝ) (c.witness.ub:ℝ) := by
  have hp := atomExpr_positive c.terms z d.data.segments c.start c.dir (datumCheck_positive d.data dw hd).1
  have hm := cellUBF_model (latticeAtomCell z d c) c.witness hp hc
  have hb := cellUBF_spec (latticeAtomCell z d c) c.witness hp hc
  have he (u : ℝ) (hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ)) :
      (latticeAtomCell z d c).expr.value u=omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-
        2*U d.data.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)) := by
    simpa only [latticeAtomCell,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ratCast] using
      atomExpr_value c.terms z hz d.data dw hd c.start c.dir u (by simpa only [Rat.cast_one,Rat.cast_ofNat] using penaltyCell_parameter c 1 4 hl hr u hu)
  simp only [latticeAtomCell,Rat.cast_zero] at hm hb
  refine ⟨⟨hm.1,hm.2.1,?_⟩,?_⟩
  · intro u hu
    dsimp only
    rw [← he u hu]
    exact hm.2.2 u hu
  · intro u hu
    rw [← he u hu]
    exact hb u hu
#print axioms penaltyCell_integral_bound
#print axioms fullLatticeCell_source
#print axioms latticeAtomCell_source
end
end CatalanCore.Li2.DecayCert
