module
public import CatalanCore.Li2.DecayCert.Compile
public import CatalanCore.Li2.DecayCert.Density
public import CatalanCore.Li2.DecayCert.SourceBridge
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section
inductive EndCellKind | branch | off | own
noncomputable def endZ (d : SegmentData) (b e : ℂ) (D : ℝ) : ℝ :=
  ‖(b-d.M)/d.h‖+‖e/d.h‖*D
noncomputable def endPhi (d : SegmentData) (b e : ℂ) (D : ℝ) : ℝ :=
  endZ d b e D+Real.sqrt ((endZ d b e D)^2+1)
def EndCellGeometry (d : SegmentData) (b e : ℂ) (D : ℝ) : EndCellKind → Prop
  | .branch =>
      ((b-d.M)/d.h=1 ∨ (b-d.M)/d.h= -1) ∧ e ≠ 0 ∧
        (∀ τ ∈ Ioc 0 D, 1 < CatalanCore.Tools.Joukowski.jc ((b+e*(τ:ℂ)-d.M)/d.h))
  | .off =>
      ‖e/d.h‖*D < min ‖(b-d.M)/d.h-1‖ ‖(b-d.M)/d.h+1‖ ∧
        (∀ τ ∈ Icc 0 D, 1 < CatalanCore.Tools.Joukowski.jc ((b+e*(τ:ℂ)-d.M)/d.h))
  | .own => ∀ τ ∈ Icc 0 D, ∃ x ∈ Icc (-1:ℝ) 1, b+e*(τ:ℂ)=d.M+d.h*(x:ℂ)
noncomputable def endMajorant (d : SegmentData) (b e : ℂ) (D : ℝ) : EndCellKind → ℝ
  | .own => (∑ k ∈ Finset.range d.N, (k+1:ℕ)*|d.c (k+1)|)*‖e/d.h‖*D
  | kind =>
      let l := ‖e/d.h‖*D
      let Φ := endPhi d b e D
      let f := ∑ k ∈ Finset.range (d.N+1), |d.c k| *Φ^k
      let r := ∑ k ∈ Finset.range d.N, (k+1:ℕ)*|d.c (k+1)| *Φ^k
      let fac := match kind with
        | .branch => 2*Real.sqrt l/Real.sqrt (2-l)
        | .off => l/Real.sqrt ((‖(b-d.M)/d.h-1‖-l)*(‖(b-d.M)/d.h+1‖-l))
        | .own => 0
      f*fac+r*l
def intervalInside (a b x y : ℚ) : Bool := decide (a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b)

structure HolderCopyWitness where
  kind : ℕ
  gammaHi : ℚ
  zetaHi : ℚ
  phiHi : ℚ
  d1Lo : ℚ
  d2Lo : ℚ
  rootHi : ℚ
  denominatorLo : ℚ
def holderCopyBound (d : QSegment) (p e : CQ) (R : ℚ)
    (w : HolderCopyWitness) : Option ℚ :=
  let ζ := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  let l := w.gammaHi*R
  let Z := w.zetaHi+l
  let F := ((List.range d.coeff.length).map (fun k : ℕ => |d.c k| *w.phiHi^k)).sum
  let A := ((List.range (d.coeff.length-1)).map (fun k : ℕ =>
    (k+1:ℚ)*|d.c (k+1)| *w.phiHi^k)).sum
  if cqSq d.half=0 ∨ R < 0 ∨ w.gammaHi < 0 ∨ w.zetaHi < 0 ∨
      w.gammaHi^2 < cqSq γ ∨ w.zetaHi^2 < cqSq ζ ∨
      w.phiHi < Z ∨ (w.phiHi-Z)^2 < Z^2+1 then none
  else if w.kind=0 then
    if ζ.2=0 ∧ γ.2=0 ∧ intervalInside (-1) 1 ζ.1 (ζ.1+γ.1*R) then
      some (((List.range (d.coeff.length-1)).map (fun k : ℕ => (k+1:ℚ)*|d.c (k+1)|)).sum*l)
    else none
  else if w.kind=1 then
    if (ζ=(1,0) ∨ ζ=(-1,0)) ∧ 0 ≤ l ∧ l < 1 ∧
      (γ.2 ≠ 0 ∨ (ζ=(1,0) ∧ 0 < γ.1) ∨ (ζ=(-1,0) ∧ γ.1 < 0)) ∧
      0 ≤ w.rootHi ∧ l ≤ w.rootHi^2 ∧ 0 < w.denominatorLo ∧ w.denominatorLo^2 ≤ 2-l
    then some (2*F*w.rootHi/w.denominatorLo+A*l) else none
  else if w.kind=2 then
    if 0 ≤ l ∧ l^2 < slitDistSq ζ ∧ l < w.d1Lo ∧ l < w.d2Lo ∧
      w.d1Lo^2 ≤ cqSq (cqSub ζ (1,0)) ∧ w.d2Lo^2 ≤ cqSq (cqAdd ζ (1,0)) ∧
      0 < w.denominatorLo ∧ w.denominatorLo^2 ≤ (w.d1Lo-l)*(w.d2Lo-l)
    then some (F*l/w.denominatorLo+A*l) else none
  else none

structure HolderCellWitness where
  field : CellWitness
  points : List CellWitness
  copies : List HolderCopyWitness
structure NodeCell where
  p : CQ
  e : CQ
  width : ℚ
  scale : ℤ
  terms : ℕ
inductive FieldMethod
  | taylor : CellWitness → FieldMethod
  | holder : HolderCellWitness → FieldMethod

def makeCell (c : NodeCell) (e : CellExpr) : CellInput := ⟨e,0,c.width,c.scale⟩
def endpointCell (c : NodeCell) (e : CellExpr) : CellInput := ⟨e,0,0,c.scale⟩
def holderCellBounds (z : ℚ) (d : SegmentDatum) (c : NodeCell)
    (w : HolderCellWitness) : Option QBox := do
  if ¬(0 < c.width ∧ w.points.length=d.segments.length ∧ w.copies.length=d.segments.length)
    then none else
    if cellUBF (makeCell c (fieldExpr c.terms z c.p c.e)) w.field=false then none else
      let bounds ← (List.range d.segments.length).mapM (fun j => do
        let s ← d.segments[j]?
        let p ← w.points[j]?
        let h ← w.copies[j]?
        if cellUBF (endpointCell c (.segment s c.p c.e)) p=false then none else
          let H ← holderCopyBound s c.p c.e c.width h
          pure (p.lb-H,p.ub+H))
      pure (w.field.lb+2*(bounds.map Prod.fst).sum,
        w.field.ub+2*(bounds.map Prod.snd).sum)
def fieldCellBounds (z : ℚ) (d : SegmentDatum) (c : NodeCell) : FieldMethod → Option QBox
  | .taylor w =>
      if cellUBF (makeCell c (WExpr c.terms z d.segments c.p c.e)) w then some (w.lb,w.ub) else none
  | .holder w => holderCellBounds z d c w

theorem endZ_nonneg (d : SegmentData) (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ endZ d b e D := add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hD)
theorem endPhi_one_le (d : SegmentData) (b e : ℂ) (D : ℝ) (hD : 0 ≤ D) :
    1 ≤ endPhi d b e D := by
  have hZ := endZ_nonneg d b e D hD
  have hs : 1 ≤ Real.sqrt ((endZ d b e D)^2+1) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ (endZ d b e D)^2+1 by nlinarith [sq_nonneg (endZ d b e D)])
  unfold endPhi
  linarith
#print axioms endZ_nonneg
#print axioms endPhi_one_le
end
end CatalanCore.Li2.DecayCert
