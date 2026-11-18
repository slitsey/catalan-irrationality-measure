module
public import CatalanCore.Li2.DecayCert.Holder.Defs
public import CatalanCore.Li2.DecayCert.Covers.Intervals
public import CatalanCore.Li2.DecayCert.Energy
public import CatalanCore.Li2.DecayCert.Mass
public import CatalanCore.Li2.DecayCert.FieldIntegral
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section
structure BentFrame where
  frame : CatalanCore.Li2.Uniform.DualFrame
  polygon : CatalanCore.Li2.Uniform.PolygonFrame
  hpure : frame.pure=false
  hlattice : frame.lattice=Icc 0 polygon.cut
  hfree : ∀ s : ℤ, frame.free s=CatalanCore.Li2.Uniform.polygonFree polygon s
  cut_zero : polygon.cut=0
  coord : ℕ → CQ
  coord_eq : ∀ j, j ≤ polygon.edges → cqReal (coord j)=polygon.vertex j
def BentFrame.geometry (b : BentFrame) : CatalanCore.Li2.Uniform.FrameGeometry b.frame :=
  .polygon b.polygon b.hpure b.hlattice b.hfree
structure SegmentPlacement where
  edge : ℕ
  left : ℚ
  right : ℚ
structure BentInput where
  geom : BentFrame
  upper : List QSegment
  atoms : List QSegment
  height : ℚ
  placements : List SegmentPlacement
  data : SegmentDatum
  source_eq : data.segments=upper++upper.map QSegment.conj++atoms

def baseSegments (b : BentInput) : List QSegment := b.upper++b.atoms
def edgeOrigin (b : BentInput) (j : ℕ) : CQ := b.geom.coord j
def edgeDirection (b : BentInput) (j : ℕ) : CQ :=
  if j=b.geom.polygon.edges then (0,1) else cqSub (b.geom.coord (j+1)) (b.geom.coord j)
def edgeLimit (b : BentInput) (j : ℕ) : ℚ :=
  if j=b.geom.polygon.edges then b.height-(b.geom.coord j).2 else 1

def placementCheck (b : BentInput) : Bool :=
  decide (b.upper.length=b.placements.length ∧ 1 ≤ b.height ∧
    (b.geom.coord b.geom.polygon.edges).2 ≤ b.height) &&
  ((List.range b.upper.length).all (fun j : ℕ => match b.upper[j]?,b.placements[j]? with
    | some s,some p => decide (p.edge < b.geom.polygon.edges ∧
        0 ≤ p.left ∧ p.left < p.right ∧ p.right ≤ 1 ∧
        cqSub s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.left (edgeDirection b p.edge)) ∧
        cqAdd s.mid s.half=cqAdd (edgeOrigin b p.edge) (cqScale p.right (edgeDirection b p.edge)))
    | _,_ => false)) &&
  (b.atoms.all (fun s => decide (s.mid.2=0 ∧ s.half.2=0 ∧
    -4 ≤ s.mid.1-s.half.1 ∧ s.mid.1-s.half.1 ≤ -1 ∧
    -4 ≤ s.mid.1+s.half.1 ∧ s.mid.1+s.half.1 ≤ -1)))

structure ContourCell where
  edge : ℕ
  left : ℚ
  right : ℚ
  backwards : Bool
  scale : ℤ
  terms : ℕ
  method : FieldMethod
def contourNodeCell (b : BentInput) (c : ContourCell) : NodeCell :=
  let start := if c.backwards then c.right else c.left
  let dir := if c.backwards then cqNeg (edgeDirection b c.edge) else edgeDirection b c.edge
  ⟨cqAdd (edgeOrigin b c.edge) (cqScale start (edgeDirection b c.edge)),
    dir,c.right-c.left,c.scale,c.terms⟩
def contourBounds (z : ℚ) (b : BentInput) (c : ContourCell) : Option QBox :=
  if c.edge ≤ b.geom.polygon.edges ∧ 0 ≤ c.left ∧ c.left < c.right ∧
      c.right ≤ edgeLimit b c.edge then
    fieldCellBounds z b.data (contourNodeCell b c) c.method else none

def contourCoverCheck (b : BentInput) (cs : List ContourCell) : Bool :=
  (List.range (b.geom.polygon.edges+1)).all (fun j : ℕ =>
    chainCheck 0 (edgeLimit b j) ((cs.filter (fun c => c.edge==j)).map (fun c => ⟨c.left,c.right⟩))) &&
    cs.all (fun c => decide (c.edge ≤ b.geom.polygon.edges))

structure AtomCell where
  left : ℚ
  right : ℚ
  backwards : Bool
  scale : ℤ
  terms : ℕ
  witness : LineWitness
def AtomCell.start (c : AtomCell) : ℚ := if c.backwards then c.right else c.left
def AtomCell.dir (c : AtomCell) : ℚ := if c.backwards then -1 else 1
def atomCellInput (z : ℚ) (d : SegmentDatum) (c : AtomCell) : CellInput :=
  ⟨atomExpr c.terms z d.segments c.start c.dir,0,c.right-c.left,c.scale⟩
def atomCellCheck (z : ℚ) (d : SegmentDatum) (c : AtomCell) : Bool :=
  decide (1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4) &&
    lineCellF (atomCellInput z d c) c.witness
def atomCoverCheck (z : ℚ) (d : SegmentDatum) (cs : List AtomCell) : Bool :=
  chainCheck 1 4 (cs.map (fun c => ⟨c.left,c.right⟩)) && cs.all (atomCellCheck z d)
def atomPosSum (cs : List AtomCell) (ρ lam : ℚ) : ℚ :=
  (cs.map (fun c => linePos c.witness.a c.witness.b (c.right-c.left) (ρ+lam))).sum

structure EnergyPiece where
  segment : ℕ
  left : ArcPoint
  right : ArcPoint
  parents : List ℕ
  terms : ℕ

def energyCoverCheck (b : BentInput) (es : List EnergyPiece) : Bool :=
  es.all (fun e => decide (e.segment < (baseSegments b).length ∧ e.parents ≠ []) && e.left.valid && e.right.valid) &&
  ((List.range (baseSegments b).length).all (fun j : ℕ =>
    chainCheck (-1) 1 ((es.filter (fun e => e.segment==j)).map (fun e => ⟨e.left.x,e.right.x⟩))))
-- General lower bound on a chain of clipped parent intervals. Parent order is checked.
def clippedParentLower (lo hi : ℚ) (rows : List (QInterval × ℚ)) : Option ℚ :=
  let clipped := (rows.map (fun r => ((⟨max lo r.1.left,min hi r.1.right⟩ : QInterval),r.2))).filter (fun r => r.1.left < r.1.right)
  match clipped with
  | [] => none
  | r::rs =>
      if chainCheck lo hi ((r::rs).map Prod.fst) then
        some (rs.foldl (fun v r => min v r.2) r.2) else none

def energyLower (z : ℚ) (b : BentInput) (cc : List ContourCell) (ac : List AtomCell)
    (e : EnergyPiece) : Option ℚ := do
  let s ← (baseSegments b)[e.segment]?
  if e.parents=[] then none else
  if e.segment < b.upper.length then
    let p ← b.placements[e.segment]?
    let t (x : ℚ) := (p.left+p.right)/2+(p.right-p.left)*x/2
    let rows ← e.parents.mapM (fun j : ℕ => do
      let parent ← cc[j]?
      if p.edge ≠ parent.edge then none else
        let B ← contourBounds z b parent
        pure (⟨parent.left,parent.right⟩,B.1))
    clippedParentLower (min (t e.left.x) (t e.right.x))
      (max (t e.left.x) (t e.right.x)) rows
  else
    let x (t : ℚ) := -s.mid.1-s.half.1*t
    let rows ← e.parents.mapM (fun j : ℕ => do
      let parent ← ac[j]?
      if atomCellCheck z b.data parent=false then none else
        pure (⟨parent.left,parent.right⟩,parent.witness.cell.lb))
    clippedParentLower (min (x e.left.x) (x e.right.x))
      (max (x e.left.x) (x e.right.x)) rows

structure BentCert where
  density : DensityWitness
  atomCaps : List AtomCapWitness
  contour : List ContourCell
  atoms : List AtomCell
  energyCells : List EnergyPiece
  vSeeds : List (VSeed×VSeed×VSeed)
  ell : ℚ
  Iup : ℚ
  terms : ℕ


theorem contourNodeCell_width (b : BentInput) (c : ContourCell) :
    (contourNodeCell b c).width=c.right-c.left := rfl

theorem baseSegments_mem_data (b : BentInput) (s : QSegment) (hs : s ∈ baseSegments b) :
    s ∈ b.data.segments := by
  rw [b.source_eq]
  rcases List.mem_append.mp hs with hu | ha
  · exact List.mem_append_left _ (List.mem_append_left _ hu)
  · exact List.mem_append_right _ ha

theorem baseSegments_positive (b : BentInput) (w : DensityWitness) (hd : datumCheck b.data w=true) :
    ∀ s ∈ baseSegments b,∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) x := by
  intro s hs
  exact (datumCheck_positive b.data w hd).1 s (baseSegments_mem_data b s hs)
#print axioms baseSegments_mem_data
#print axioms baseSegments_positive
end
end CatalanCore.Li2.DecayCert
