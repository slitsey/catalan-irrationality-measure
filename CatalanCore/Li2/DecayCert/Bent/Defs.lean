module
public import CatalanCore.Li2.DecayCert.BentSpec
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section
def oneVExpr (z : ℚ) (s : QSegment) (w : VSeed×VSeed×VSeed) (terms : ℕ) : SE :=
  let ms := cqAdd (cqScale (s.c 0) s.mid) (cqScale (s.c 1/2) s.half)
  seAdd (seSum [seScale 3 (vintExpr s 1 w.1),seScale (-2) (vintExpr s 0 w.2.1),
      seNeg (vintExpr s 4 w.2.2)])
    (seSub (seScale ms.1 (.log terms |z|)) (seScale |ms.2| .pi))
def bentVExpr (z : ℚ) (b : BentInput) (c : BentCert) : Option SE := do
  if c.vSeeds.length ≠ (baseSegments b).length then none else
    let es ← (List.range (baseSegments b).length).mapM (fun j : ℕ => do
      let s ← (baseSegments b)[j]?
      let w ← c.vSeeds[j]?
      if vintGeometryCheck s 1 w.1 && vintGeometryCheck s 0 w.2.1 &&
          vintGeometryCheck s 4 w.2.2 then
        pure (seScale (if j < b.upper.length then 2 else 1) (oneVExpr z s w c.terms))
      else none)
    pure (seSum es)
def bentEnergyExpr (z : ℚ) (b : BentInput) (c : BentCert) : Option SE := do
  let VI ← bentVExpr z b c
  let lows ← c.energyCells.mapM (fun e => do
    let s ← (baseSegments b)[e.segment]?
    let lo ← energyLower z b c.contour c.atoms e
    pure (seScale ((if e.segment < b.upper.length then 2 else 1)*lo)
      (arcMassExpr e.terms s e.left e.right)))
  pure (seScale (1/2) (seSub VI (seSum lows)))
def bentTailExpr (b : BentInput) (c : BentCert) : SE :=
  let x := (b.geom.coord b.geom.polygon.edges).1
  seSum [seScale 3 (.log c.terms (x+b.height+1)),seScale (-4) (.log c.terms b.height),
    seScale 4 (.log c.terms (x+b.height+b.data.radius)),seScale (-b.height) .pi]
def bentSegmentCheck (z : ℚ) (b : BentInput) (c : BentCert) : Bool :=
  decide (-1 < z ∧ z < 0 ∧ c.atomCaps.length=b.atoms.length) &&
  ((List.range b.atoms.length).all (fun j : ℕ => match b.atoms[j]?,c.atomCaps[j]? with
    | some a,some w => atomCapCheck a w | _,_ => false)) &&
  datumCheck b.data c.density && placementCheck b &&
  contourCoverCheck b c.contour &&
  c.contour.all (fun cell => match contourBounds z b cell with
    | some B => decide (B.2 ≤ c.ell) | none => false) &&
  atomCoverCheck z b.data c.atoms && energyCoverCheck b c.energyCells &&
  scalarUpperCheck (bentTailExpr b c) c.ell &&
  (match bentEnergyExpr z b c with | some e => scalarUpperCheck e c.Iup | none => false)
def bentPairCheck (c : BentCert) (ρ lam D : ℚ) : Bool :=
  decide (0 < ρ ∧ c.ell ≤ lam) && scalarLowerCheck D
    (seSum [seScale (-12) (.log c.terms 2),seRat (-4-c.Iup-2*lam-atomPosSum c.atoms ρ lam)])

#print axioms bentSegmentCheck
#print axioms bentPairCheck
end
end CatalanCore.Li2.DecayCert
