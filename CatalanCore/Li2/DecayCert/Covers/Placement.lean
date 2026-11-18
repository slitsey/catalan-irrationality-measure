module
public import CatalanCore.Li2.DecayCert.Covers.Physical
public import CatalanCore.Li2.DecayCert.Covers.ParentPoint
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem placementCheck_upper_row (b : BentInput) (hp : placementCheck b=true) (j : ℕ)
    (hj : j < b.upper.length) (s : QSegment) (p : SegmentPlacement)
    (hs : b.upper[j]?=some s) (hpl : b.placements[j]?=some p) :
    p.edge < b.geom.polygon.edges ∧ 0 ≤ p.left ∧ p.left < p.right ∧ p.right ≤ 1 ∧
      cqSub s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.left (edgeDirection b p.edge)) ∧
      cqAdd s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.right (edgeDirection b p.edge)) := by
  have h := hp
  simp only [placementCheck,Bool.and_eq_true] at h
  have hrow := (List.all_eq_true.mp h.1.2) j (List.mem_range.mpr hj)
  simp only [hs,hpl] at hrow
  exact of_decide_eq_true hrow

theorem placementCheck_atom (b : BentInput) (hp : placementCheck b=true) (s : QSegment) (hs : s ∈ b.atoms) :
    s.mid.2=0 ∧ s.half.2=0 ∧ -4 ≤ s.mid.1-s.half.1 ∧ s.mid.1-s.half.1 ≤ -1 ∧
      -4 ≤ s.mid.1+s.half.1 ∧ s.mid.1+s.half.1 ≤ -1 := by
  have h := hp
  simp only [placementCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true ((List.all_eq_true.mp h.2) s hs)

theorem placement_source_point (b : BentInput) (s : QSegment) (p : SegmentPlacement)
    (hl : cqSub s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.left (edgeDirection b p.edge)))
    (hr : cqAdd s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.right (edgeDirection b p.edge))) (x : ℝ) :
    cqReal s.mid+cqReal s.half*(x:ℂ)=cqReal (edgeOrigin b p.edge)+cqReal (edgeDirection b p.edge)*
      ((((p.left:ℝ)+(p.right:ℝ))/2+((p.right:ℝ)-(p.left:ℝ))*x/2:ℝ):ℂ) := by
  have hleft := congrArg cqReal hl
  have hright := congrArg cqReal hr
  simp only [cqReal_sub,cqReal_add,cqReal_scale] at hleft hright
  push_cast
  linear_combination (1-(x:ℂ))/2*hleft+(1+(x:ℂ))/2*hright

theorem atom_source_point (s : QSegment) (hm : s.mid.2=0) (hh : s.half.2=0) (x : ℝ) :
    cqReal s.mid+cqReal s.half*(x:ℂ)= -(((-(s.mid.1:ℝ)-(s.half.1:ℝ)*x:ℝ)):ℂ) := by
  simp only [cqReal,hm,hh,Rat.cast_zero,zero_mul,add_zero]
  push_cast
  ring

theorem real_affine_mem_between (a b x l r : ℝ) (hx : x ∈ Icc l r) :
    a+b*x ∈ Icc (min (a+b*l) (a+b*r)) (max (a+b*l) (a+b*r)) := by
  by_cases hb : 0 ≤ b
  · constructor
    · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.1)])
    · exact (show a+b*x ≤ a+b*r by nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.2)]).trans (le_max_right _ _)
  · have hb' : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
    constructor
    · exact (min_le_right _ _).trans (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' (sub_nonneg.mpr hx.2)])
    · exact (show a+b*x ≤ a+b*l by nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' (sub_nonneg.mpr hx.1)]).trans (le_max_left _ _)
#print axioms placementCheck_upper_row
#print axioms placementCheck_atom
#print axioms placement_source_point
#print axioms atom_source_point
#print axioms real_affine_mem_between
end
end CatalanCore.Li2.DecayCert
