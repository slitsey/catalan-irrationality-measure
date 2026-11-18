module
public import CatalanCore.Li2.DecayCert.Bent

@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay
noncomputable section

/-- Projections of an abstract contour cell: the edge it lies on and its parameter interval. -/
class ContourProj (CC : Type) where
  edge : CC → ℕ
  left : CC → ℚ
  right : CC → ℚ

/-- Projections of an abstract atom cell: its interval on the atom line `[1,4]`. -/
class AtomProj (AC : Type) where
  left : AC → ℚ
  right : AC → ℚ

/-- Stored output of an atom cell: orientation, the dominating line `a + b u`, and the `W` bounds. -/
structure AtomOut where
  backwards : Bool
  a : ℚ
  b : ℚ
  lb : ℚ
  ub : ℚ

def AtomOut.start (o : AtomOut) (l r : ℚ) : ℚ := if o.backwards then r else l
def AtomOut.dir (o : AtomOut) : ℚ := if o.backwards then -1 else 1

/-- Generic certificate: each cell is stored with its own output, certified elsewhere, cell by cell. -/
structure NodeCert (CC AC : Type) where
  density : DensityWitness
  atomCaps : List AtomCapWitness
  contour : List (CC × QBox)
  atoms : List (AC × AtomOut)
  energyCells : List EnergyPiece
  vSeeds : List (VSeed×VSeed×VSeed)
  ell : ℚ
  Iup : ℚ
  terms : ℕ

/-- The cell-free part of a node certificate, in the shape of the old `BentCert` (cells forgotten). -/
def NodeCert.toBent {CC AC : Type} (c : NodeCert CC AC) : BentCert :=
  ⟨c.density,c.atomCaps,[],[],c.energyCells,c.vSeeds,c.ell,c.Iup,c.terms⟩

variable {CC AC : Type} [ContourProj CC] [AtomProj AC]

/-- Per-cell contour facts: `W` on the cell's segment of its edge lies in the stored box. -/
def NodeContourPhysical (z : ℚ) (b : BentInput) (cs : List (CC × QBox)) : Prop :=
  ∀ x ∈ cs,∀ t ∈ Icc ((ContourProj.left x.1:ℚ):ℝ) ((ContourProj.right x.1:ℚ):ℝ),
    W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b (ContourProj.edge x.1))+
      cqReal (edgeDirection b (ContourProj.edge x.1))*(t:ℂ)) ∈ Icc (x.2.1:ℝ) (x.2.2:ℝ)

/-- Per-cell atom facts, `W` part: `W` on the cell's interval lies in the stored `[lb,ub]`. -/
def NodeAtomWPhysical (z : ℚ) (b : BentInput) (cs : List (AC × AtomOut)) : Prop :=
  ∀ x ∈ cs,∀ t ∈ Icc ((AtomProj.left x.1:ℚ):ℝ) ((AtomProj.right x.1:ℚ):ℝ),
    W (z:ℝ) b.data.dual.σ (-(t:ℂ)) ∈ Icc (x.2.lb:ℝ) (x.2.ub:ℝ)

/-- Per-cell atom facts, line part: the stored line `a + b u` dominates the atom integrand. -/
def NodeAtomLinePhysical (z : ℚ) (b : BentInput) (cs : List (AC × AtomOut)) : Prop :=
  ∀ x ∈ cs,∀ u ∈ Icc (0:ℝ) ((AtomProj.right x.1-AtomProj.left x.1:ℚ):ℝ),
    omega (z:ℝ) (((x.2.start (AtomProj.left x.1) (AtomProj.right x.1):ℚ):ℝ)+((x.2.dir:ℚ):ℝ)*u)-
      2*U b.data.dual.σ (-((((x.2.start (AtomProj.left x.1) (AtomProj.right x.1):ℚ):ℝ)+
        ((x.2.dir:ℚ):ℝ)*u:ℝ):ℂ)) ≤ (x.2.a:ℝ)+(x.2.b:ℝ)*u

/-- Cover check on the contour projections (iterates over cells, evaluates none). -/
def nodeContourCoverCheck (b : BentInput) (cs : List (CC × QBox)) : Bool :=
  (List.range (b.geom.polygon.edges+1)).all (fun j : ℕ =>
    chainCheck 0 (edgeLimit b j) ((cs.filter (fun c => ContourProj.edge c.1==j)).map
      (fun c => ⟨ContourProj.left c.1,ContourProj.right c.1⟩))) &&
    cs.all (fun c => decide (ContourProj.edge c.1 ≤ b.geom.polygon.edges))

def nodeAtomCoverCheck (cs : List (AC × AtomOut)) : Bool :=
  chainCheck 1 4 (cs.map (fun c => ⟨AtomProj.left c.1,AtomProj.right c.1⟩))

def nodeAtomPosSum (cs : List (AC × AtomOut)) (ρ lam : ℚ) : ℚ :=
  (cs.map (fun c => linePos c.2.a c.2.b (AtomProj.right c.1-AtomProj.left c.1) (ρ+lam))).sum

/-- Lower bound for an energy piece from the stored parent bounds (no cell is recomputed). -/
def nodeEnergyLower (b : BentInput) (cc : List (CC × QBox)) (ac : List (AC × AtomOut))
    (e : EnergyPiece) : Option ℚ := do
  let s ← (baseSegments b)[e.segment]?
  if e.parents=[] then none else
  if e.segment < b.upper.length then
    let p ← b.placements[e.segment]?
    let t (x : ℚ) := (p.left+p.right)/2+(p.right-p.left)*x/2
    let rows ← e.parents.mapM (fun j : ℕ => do
      let parent : CC × QBox ← cc[j]?
      if p.edge ≠ ContourProj.edge parent.1 then none else
        pure (⟨ContourProj.left parent.1,ContourProj.right parent.1⟩,parent.2.1))
    clippedParentLower (min (t e.left.x) (t e.right.x))
      (max (t e.left.x) (t e.right.x)) rows
  else
    let x (t : ℚ) := -s.mid.1-s.half.1*t
    let rows ← e.parents.mapM (fun j : ℕ => do
      let parent : AC × AtomOut ← ac[j]?
      pure (⟨AtomProj.left parent.1,AtomProj.right parent.1⟩,parent.2.lb))
    clippedParentLower (min (x e.left.x) (x e.right.x))
      (max (x e.left.x) (x e.right.x)) rows

def nodeEnergyExpr (z : ℚ) (b : BentInput) (c : NodeCert CC AC) : Option SE := do
  let VI ← bentVExpr z b c.toBent
  let lows ← c.energyCells.mapM (fun e => do
    let s ← (baseSegments b)[e.segment]?
    let lo ← nodeEnergyLower b c.contour c.atoms e
    pure (seScale ((if e.segment < b.upper.length then 2 else 1)*lo)
      (arcMassExpr e.terms s e.left e.right)))
  pure (seScale (1/2) (seSub VI (seSum lows)))

/-- All non-cell checks of the bent node. -/
def nodeSegmentCheck (z : ℚ) (b : BentInput) (c : NodeCert CC AC) : Bool :=
  decide (-1 < z ∧ z < 0 ∧ c.atomCaps.length=b.atoms.length) &&
  ((List.range b.atoms.length).all (fun j : ℕ => match b.atoms[j]?,c.atomCaps[j]? with
    | some a,some w => atomCapCheck a w | _,_ => false)) &&
  datumCheck b.data c.density && placementCheck b &&
  nodeContourCoverCheck b c.contour &&
  c.contour.all (fun cell => decide (cell.2.2 ≤ c.ell)) &&
  nodeAtomCoverCheck c.atoms && energyCoverCheck b c.energyCells &&
  scalarUpperCheck (bentTailExpr b c.toBent) c.ell &&
  (match nodeEnergyExpr z b c with | some e => scalarUpperCheck e c.Iup | none => false)

def nodePairCheck (c : NodeCert CC AC) (ρ lam D : ℚ) : Bool :=
  decide (0 < ρ ∧ c.ell ≤ lam) && scalarLowerCheck D
    (seSum [seScale (-12) (.log c.terms 2),seRat (-4-c.Iup-2*lam-nodeAtomPosSum c.atoms ρ lam)])

end
end CatalanCore.Li2.DecayCert.Seg
