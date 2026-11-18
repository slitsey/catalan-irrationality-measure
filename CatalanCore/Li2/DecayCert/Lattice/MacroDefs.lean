module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Leaves
public import CatalanCore.Li2.DecayCert.Lattice.Gates.RightMacro
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Energy
public import CatalanCore.Li2.DecayCert.Lattice.Chain
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial Set MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeMacro
open CatalanCore.Li2.Decay LatticeGate BernsteinGrid
noncomputable section

def thresholdPenaltyQ (S err lo hi : ℤ) (a b kappa : ℚ)
    (boxes : List (ℤ×ℤ)) : ℚ :=
  if (hi:ℚ)/(S:ℚ)≤kappa then 0
  else if kappa≤(lo:ℚ)/(S:ℚ) then
    max ((b-a)*(upperMeanQ (decodedBoxes S boxes)+(err:ℚ)/(S:ℚ)-kappa)) 0
  else (b-a)*max ((hi:ℚ)/(S:ℚ)-kappa) 0

structure Leaf where
  path : List Bool
  error : ℤ
  lower : ℤ
  upper : ℤ
  boxes : List (ℤ×ℤ)

def Leaf.normalInterval (l : Leaf) : ℚ×ℚ := childInterval l.path (-1) 1

def Leaf.interval (l : Leaf) (p r : ℚ) : QInterval :=
  ⟨p+r*l.normalInterval.1,p+r*l.normalInterval.2⟩

def Leaf.check (l : Leaf) (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ)) : Bool :=
  macroLeafCheck S w root l.path l.error l.lower l.upper l.boxes

def Leaf.penalty (l : Leaf) (S : ℤ) (r kappa : ℚ) : ℚ :=
  r*thresholdPenaltyQ S l.error l.lower l.upper l.normalInterval.1 l.normalInterval.2 kappa l.boxes

structure WParent where
  terms : ℕ
  point : ℚ
  radius : ℚ
  center : ℚ
  sourceLeft : ℚ
  sourceRight : ℚ
  sourceRadius : ℚ
  moments : List ℚ
  order : ℕ
  jetOrder : ℕ
  base : ModelWitness
  scale : ℤ
  witness : CellWitness
  boxes : List (ℤ×ℤ)
noncomputable def WParent.check (p : WParent) (z : ℚ) (d : LatticeInput) : Bool :=
  decide (0<p.radius) && WMacroParentCheck p.terms z d p.point p.radius p.center
    p.sourceLeft p.sourceRight p.sourceRadius p.moments p.order p.jetOrder p.base p.scale p.witness p.boxes

structure AtomParent where
  terms : ℕ
  point : ℚ
  radius : ℚ
  phi : ℚ
  supportEnd : ℚ
  sourceRadius : ℚ
  moments : List ℚ
  order : ℕ
  base : ModelWitness
  scale : ℤ
  witness : CellWitness
  boxes : List (ℤ×ℤ)
noncomputable def AtomParent.check (p : AtomParent) (z : ℚ) (d : LatticeInput) : Bool :=
  decide (0<p.radius) && atomMacroParentCheck p.terms z d p.point p.radius p.phi
    p.supportEnd p.sourceRadius p.moments p.order p.base p.scale p.witness p.boxes

structure RightParent where
  cell : RightCell
  center : ℚ
  sourceLeft : ℚ
  sourceRight : ℚ
  sourceRadius : ℚ
  moments : List ℚ
  order : ℕ
  jetOrder : ℕ
  base : ModelWitness
  scale : ℤ
  witness : CellWitness
  boxes : List (ℤ×ℤ)
noncomputable def RightParent.check (p : RightParent) (z : ℚ) (d : LatticeInput) : Bool :=
  rightMacroParentCheck z d p.cell p.center p.sourceLeft p.sourceRight p.sourceRadius
    p.moments p.order p.jetOrder p.base p.scale p.witness p.boxes

inductive WCell where
  | physical : PenaltyCell → WCell
  | macro : WParent → Leaf → WCell
inductive AtomCell where
  | physical : PenaltyCell → AtomCell
  | macro : AtomParent → Leaf → AtomCell
inductive RCell where
  | physical : RightCell → RCell
  | macro : RightParent → Leaf → RCell

def WCell.interval : WCell → QInterval
  | .physical c => ⟨c.left,c.right⟩
  | .macro p l => l.interval p.point p.radius
noncomputable def WCell.check (z : ℚ) (d : LatticeInput) : WCell → Bool
  | .physical c => cellUBF (fullLatticeCell z d c) c.witness
  | .macro p l => p.check z d && l.check p.scale p.witness p.boxes
def WCell.penalty (kappa : ℚ) : WCell → ℚ
  | .physical c => penaltyBoundQ c.scale c.witness (c.right-c.left) kappa
  | .macro p l => l.penalty p.scale p.radius kappa

def AtomCell.interval : AtomCell → QInterval
  | .physical c => ⟨c.left,c.right⟩
  | .macro p l => l.interval p.point p.radius
noncomputable def AtomCell.check (z : ℚ) (d : LatticeInput) : AtomCell → Bool
  | .physical c => cellUBF (latticeAtomCell z d c) c.witness
  | .macro p l => p.check z d && l.check p.scale p.witness p.boxes
def AtomCell.penalty (kappa : ℚ) : AtomCell → ℚ
  | .physical c => penaltyBoundQ c.scale c.witness (c.right-c.left) kappa
  | .macro p l => l.penalty p.scale p.radius kappa

def RCell.interval : RCell → QInterval
  | .physical c => ⟨c.left,c.right⟩
  | .macro p l => l.interval (rightCenter p.cell) (rightRadius p.cell)
noncomputable def RCell.check (z : ℚ) (d : LatticeInput) : RCell → Bool
  | .physical c => rightCellCheck z d c
  | .macro p l => p.check z d && l.check p.scale p.witness p.boxes
def RCell.penalty (kappa : ℚ) : RCell → ℚ
  | .physical c => penaltyBoundQ c.scale c.witness (c.right-c.left) kappa
  | .macro p l => l.penalty p.scale (rightRadius p.cell) kappa
end
end CatalanCore.Li2.DecayCert.LatticeMacro

namespace CatalanCore.Li2.DecayCert
open LatticeMacro LatticeGate
structure MacroLatticeSetup where
  density : DensityWitness
  energy : LatticeEnergyWitness
  energyScale : ℤ
  ordinaryMoments : List ℚ
  stieltjesMoments : List ℚ
  crossUpper : List ℤ
  theta : ℚ
  Iup : ℚ
  cutoff : ℚ
  supportCells : List WCell
  rightCells : List RCell
  terms : ℕ

def MacroLatticeSetup.tailSetup (c : MacroLatticeSetup) : LatticeSetup :=
  ⟨c.density,c.energy,c.theta,c.Iup,c.cutoff,[],[],c.terms⟩
noncomputable def macroSetupCheck (z : ℚ) (d : LatticeInput) (c : MacroLatticeSetup) : Bool :=
  decide (0 < |z| ∧ |z| < 1 ∧ 1≤c.cutoff ∧ d.Y≤c.cutoff) &&
  latticeShapeCheck d && datumCheck d.data c.density &&
  chainCheck 0 d.Y (c.supportCells.map WCell.interval) && c.supportCells.all (WCell.check z d) &&
  chainCheck d.Y c.cutoff (c.rightCells.map RCell.interval) && c.rightCells.all (RCell.check z d) &&
  scalarUpperCheck (latticeTailExpr z d c.tailSetup) c.theta &&
  scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0 &&
  energyTableCheck d c.energy c.energyScale c.ordinaryMoments c.stieltjesMoments c.crossUpper c.Iup

def macroPW (c : MacroLatticeSetup) : ℚ :=
  (c.supportCells.map (WCell.penalty c.theta)).sum+(c.rightCells.map (RCell.penalty c.theta)).sum
structure MacroLatticeCert where
  atomCells : List LatticeMacro.AtomCell
  rho : ℚ
  lower : ℚ

def macroPA (c : MacroLatticeSetup) (p : MacroLatticeCert) : ℚ :=
  (p.atomCells.map (AtomCell.penalty (p.rho+c.theta))).sum
noncomputable def macroCheck (z : ℚ) (d : LatticeInput) (c : MacroLatticeSetup) (p : MacroLatticeCert) : Bool :=
  decide (0<p.rho) && chainCheck 1 4 (p.atomCells.map AtomCell.interval) &&
  p.atomCells.all (AtomCell.check z d) &&
  scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
    seRat (-4-c.Iup-2*c.theta-2*macroPW c-macroPA c p)])
structure MacroLatticePackage where
  z : ℚ
  input : LatticeInput
  setup : MacroLatticeSetup
  checked : macroSetupCheck z input setup=true
#print axioms macroSetupCheck
#print axioms macroCheck
end CatalanCore.Li2.DecayCert
