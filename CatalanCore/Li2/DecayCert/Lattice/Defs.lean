module
public import CatalanCore.Li2.DecayCert.BentSpec
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section
structure LatticeInput where
  data : SegmentDatum
  first : QSegment
  second : QSegment
  source_eq : data.segments=[first,second]
  Y : ℚ

def latticeShapeCheck (d : LatticeInput) : Bool :=
  decide (0 < d.Y ∧ d.first.mid=(d.Y/2,0) ∧ d.first.half=(d.Y/2,0) ∧
    d.second.mid.2=0 ∧ d.second.half.2=0 ∧
    -4 ≤ d.second.mid.1-d.second.half.1 ∧ d.second.mid.1-d.second.half.1 ≤ -1 ∧
    -4 ≤ d.second.mid.1+d.second.half.1 ∧ d.second.mid.1+d.second.half.1 ≤ -1)

def realSegMoment (d : QSegment) (y0 : ℚ) (k : ℕ) : ℚ :=
  arcPolyMoment (d.density*(Polynomial.C (d.mid.1-y0)+Polynomial.C d.half.1*Polynomial.X)^k)
structure LatticeEnergyWitness where
  phi : ℚ
  order : ℕ
  terms : ℕ

def selfEnergyExpr (terms : ℕ) (d : QSegment) : SE :=
  seAdd (seScale ((d.c 0)^2) (seSub (.log terms 2) (.log terms |d.half.1|)))
    (seRat (((List.range (d.coeff.length-1)).map (fun k : ℕ => (d.c (k+1))^2/(2*(k+1:ℚ)))).sum))
def latticeEnergyExpr (d : LatticeInput) (w : LatticeEnergyWitness) : Option SE :=
  let ξ := (w.phi+w.phi⁻¹)/2
  let y0 := d.first.mid.1-d.first.half.1*ξ
  let H := |d.second.mid.1-y0|+|d.second.half.1|
  let v := H/(-y0)
  if 1 < w.phi ∧ y0 < 0 ∧ 0 ≤ v ∧ v < 1 then
    let U0 := seAdd (seScale (d.first.c 0)
      (seSub (seSub (.log w.terms 2) (.log w.terms d.first.half.1)) (.log w.terms w.phi)))
      (seRat (((List.range (d.first.coeff.length-1)).map (fun k : ℕ =>
        d.first.c (k+1)*(-1:ℚ)^(k+1)*w.phi^(-(k+1:ℤ))/(k+1:ℚ))).sum))
    let cross := ((List.range w.order).map (fun k : ℕ =>
      realSegMoment d.second y0 (k+1)*stieltjesQ d.first w.phi (k+1)/(k+1:ℚ))).sum
    let err := 2*d.second.c 0*d.first.c 0*v^(w.order+1)/((w.order+1:ℚ)*(1-v))
    some (seSum [selfEnergyExpr w.terms d.first,selfEnergyExpr w.terms d.second,
      seScale (2*d.second.c 0) U0,seRat (2*cross+err)])
  else none

structure PenaltyCell where
  left : ℚ
  right : ℚ
  backwards : Bool
  scale : ℤ
  terms : ℕ
  witness : CellWitness
def PenaltyCell.start (c : PenaltyCell) : ℚ := if c.backwards then c.right else c.left
def PenaltyCell.dir (c : PenaltyCell) : ℚ := if c.backwards then -1 else 1

def integralModelQ (co : List ℚ) (R : ℚ) : ℚ :=
  ((List.range co.length).map (fun j : ℕ => coeffQ co j*R^(j+1)/(j+1:ℚ))).sum
def penaltyBoundQ (S : ℤ) (w : CellWitness) (R κ : ℚ) : ℚ :=
  if w.ub ≤ κ then 0
  else if κ ≤ w.lb then max (integralModelQ (gridCoeffs S w) R+w.remainder*R-κ*R) 0
  else R*max (w.ub-κ) 0

def fullLatticeCell (z : ℚ) (d : LatticeInput) (c : PenaltyCell) : CellInput :=
  ⟨WExpr c.terms z d.data.segments (c.start,0) (c.dir,0),0,c.right-c.left,c.scale⟩
def latticeAtomCell (z : ℚ) (d : LatticeInput) (c : PenaltyCell) : CellInput :=
  ⟨atomExpr c.terms z d.data.segments c.start c.dir,0,c.right-c.left,c.scale⟩
structure RightCell where
  left : ℚ
  right : ℚ
  r : ℚ
  scale : ℤ
  terms : ℕ
  witness : CellWitness

def rightCellSource (z : ℚ) (d : LatticeInput) (c : RightCell) : CellExpr :=
  .add (fieldExpr c.terms z (c.left,0) (1,0))
    (.add (.scale 2 (.constant (segConstant c.terms d.first (1/c.r,0))))
      (.scale 2 (.segment d.second (c.left,0) (1,0))))
def rightCellInput (z : ℚ) (d : LatticeInput) (c : RightCell) : CellInput :=
  ⟨rightCellSource z d c,0,c.right-c.left,c.scale⟩
def rightCellCheck (z : ℚ) (d : LatticeInput) (c : RightCell) : Bool :=
  decide (d.Y ≤ c.left ∧ c.left < c.right ∧ 0 < c.r ∧ c.r < 1 ∧
    c.right=d.Y*(1+c.r)^2/(4*c.r)) && cellUBF (rightCellInput z d c) c.witness

structure LatticeSetup where
  density : DensityWitness
  energy : LatticeEnergyWitness
  theta : ℚ
  Iup : ℚ
  cutoff : ℚ
  supportCells : List PenaltyCell
  rightCells : List RightCell
  terms : ℕ

def latticeTailExpr (z : ℚ) (d : LatticeInput) (c : LatticeSetup) : SE :=
  seSum [seScale 3 (.log c.terms (c.cutoff+1)),seScale (-4) (.log c.terms c.cutoff),
    seScale c.cutoff (.log c.terms |z|),seScale 4 (.log c.terms (c.cutoff+d.data.radius))]
def latticeSetupCheck (z : ℚ) (d : LatticeInput) (c : LatticeSetup) : Bool :=
  decide (0 < |z| ∧ |z| < 1 ∧ 1 ≤ c.cutoff ∧ d.Y ≤ c.cutoff) &&
  latticeShapeCheck d && datumCheck d.data c.density &&
  chainCheck 0 d.Y (c.supportCells.map (fun x => ⟨x.left,x.right⟩)) &&
  c.supportCells.all (fun x => cellUBF (fullLatticeCell z d x) x.witness) &&
  chainCheck d.Y c.cutoff (c.rightCells.map (fun x => ⟨x.left,x.right⟩)) &&
  c.rightCells.all (rightCellCheck z d) && scalarUpperCheck (latticeTailExpr z d c) c.theta &&
  scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0 &&
  (match latticeEnergyExpr d c.energy with | some e => scalarUpperCheck e c.Iup | none => false)

def latticePW (d : LatticeInput) (c : LatticeSetup) : ℚ :=
  ((c.supportCells.map (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) c.theta)).sum) +
  ((c.rightCells.map (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) c.theta)).sum)
structure LatticeCert where
  atomCells : List PenaltyCell
  rho : ℚ
  lower : ℚ

def latticePA (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert) : ℚ :=
  (p.atomCells.map (fun x => penaltyBoundQ x.scale x.witness (x.right-x.left) (p.rho+c.theta))).sum
def latticeCheck (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert) : Bool :=
  decide (0 < p.rho) && chainCheck 1 4 (p.atomCells.map (fun x => ⟨x.left,x.right⟩)) &&
  p.atomCells.all (fun x => cellUBF (latticeAtomCell z d x) x.witness) &&
  scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
    seRat (-4-c.Iup-2*c.theta-2*latticePW d c-latticePA d c p)])

structure LatticeCoverCert where
  pairs : List LatticeCert
def latticeCoverCheck (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (p : LatticeCoverCert) : Bool := p.pairs.all (latticeCheck z d c)

#print axioms realSegMoment
#print axioms latticeSetupCheck
#print axioms latticeCheck
end
end CatalanCore.Li2.DecayCert
