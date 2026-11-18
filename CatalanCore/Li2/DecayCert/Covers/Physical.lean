module
public import CatalanCore.Li2.DecayCert.Covers.Geometry
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem contourBounds_physical (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (c : ContourCell) (B : QBox)
    (hc : contourBounds z b c=some B) :
    ∀ t ∈ Icc (c.left:ℝ) (c.right:ℝ),W (z:ℝ) b.data.dual.σ
      (cqReal (edgeOrigin b c.edge)+cqReal (edgeDirection b c.edge)*(t:ℂ)) ∈ Icc (B.1:ℝ) (B.2:ℝ) := by
  intro t ht
  let u := if c.backwards then (c.right:ℝ)-t else t-(c.left:ℝ)
  have hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ) := by
    simp only [Rat.cast_sub]
    cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith [ht.1,ht.2]
  have hparam : (if c.backwards then (c.right:ℝ)-u else (c.left:ℝ)+u)=t := by
    cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;> ring
  have hv := cellC1_okF z hz b dw hd c B hc u hu
  rw [contour_cell_parameter,hparam] at hv
  exact hv

theorem atomCell_W_physical (z : ℚ) (hz : z ≠ 0) (d : SegmentDatum)
    (dw : DensityWitness) (hd : datumCheck d dw=true) (c : AtomCell)
    (hc : atomCellCheck z d c=true) :
    ∀ x ∈ Icc (c.left:ℝ) (c.right:ℝ),W (z:ℝ) d.dual.σ (-(x:ℂ)) ∈
      Icc (c.witness.cell.lb:ℝ) (c.witness.cell.ub:ℝ) := by
  have hc' := hc
  simp only [atomCellCheck,Bool.and_eq_true,decide_eq_true_eq] at hc'
  have hline := hc'.2
  simp only [lineCellF,Bool.and_eq_true] at hline
  have hcell : cellUBF (atomCellInput z d c) c.witness.cell=true := hline.1.1
  have hp := atomExpr_positive c.terms z d.segments c.start c.dir (datumCheck_positive d dw hd).1
  intro x hx
  let u := if c.backwards then (c.right:ℝ)-x else x-(c.left:ℝ)
  have hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ) := by
    simp only [Rat.cast_sub]
    cases hb : c.backwards <;> dsimp only [u] <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;>
      constructor <;> linarith [hx.1,hx.2]
  have hparam : (c.start:ℝ)+(c.dir:ℝ)*u=x := by
    cases hb : c.backwards <;> dsimp only [u] <;>
      simp only [AtomCell.start,AtomCell.dir,hb,Bool.false_eq_true,ite_false,ite_true,Rat.cast_neg,Rat.cast_one,
        one_mul,neg_one_mul] <;> ring
  have hv := cellUBF_spec (atomCellInput z d c) c.witness.cell hp hcell u (by simpa only [atomCellInput,Rat.cast_zero] using hu)
  change (atomExpr c.terms z d.segments c.start c.dir).value u ∈ Icc (c.witness.cell.lb:ℝ) (c.witness.cell.ub:ℝ) at hv
  rw [atomExpr_value _ _ hz d dw hd _ _ u (atomCell_parameter_bounds c hc'.1 u hu)] at hv
  have hneg : -(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)= -(x:ℂ) := by rw [hparam]
  have hcoord : -(((c.start:ℝ):ℂ)+((c.dir:ℝ):ℂ)*(u:ℂ))= -(x:ℂ) := by
    have hh := congrArg (fun y : ℝ => -(y:ℂ)) hparam
    simpa only [Complex.ofReal_add,Complex.ofReal_mul] using hh
  rw [hparam,hcoord] at hv
  rw [W,atom_field_eq_extension]
  exact hv
#print axioms contourBounds_physical
#print axioms atomCell_W_physical
end
end CatalanCore.Li2.DecayCert
