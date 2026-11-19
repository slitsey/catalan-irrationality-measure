module
public import CatalanArchive.Li2.DecayCert.FixedTable.Assembly
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert

/-- Match the original producer's .all and Option-valued Boolean projections. -/
def rawSetupChecksOfAll (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (raw_setupGeometry : decide (0 < |z| ∧ |z| < 1 ∧ 1≤c.cutoff ∧ d.Y≤c.cutoff)=true)
    (raw_shape : latticeShapeCheck d=true) (raw_datum : datumCheck d.data c.density=true)
    (raw_supportChain : chainCheck 0 d.Y (c.supportCells.map (fun x => ⟨x.left,x.right⟩))=true)
    (raw_supportCells : c.supportCells.all (fun x => cellUBF (fullLatticeCell z d x) x.witness)=true)
    (raw_rightChain : chainCheck d.Y c.cutoff (c.rightCells.map (fun x => ⟨x.left,x.right⟩))=true)
    (raw_rightCells : c.rightCells.all (rightCellCheck z d)=true)
    (raw_tail : scalarUpperCheck (latticeTailExpr z d c) c.theta=true)
    (raw_slope : scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0=true)
    (raw_energy : (match latticeEnergyExpr d c.energy with |some e=>scalarUpperCheck e c.Iup|none=>false)=true) :
    RawLatticeSetupChecks z d c where
  domain := raw_setupGeometry
  shape := raw_shape
  density := raw_datum
  supportChain := raw_supportChain
  supportCell := List.all_eq_true.mp raw_supportCells
  rightChain := raw_rightChain
  rightCell := List.all_eq_true.mp raw_rightCells
  tail := raw_tail
  slope := raw_slope
  energy := by
    cases he : latticeEnergyExpr d c.energy with
    | none => simp only [he,Bool.false_eq_true] at raw_energy
    | some e => exact ⟨e,rfl,by simpa only [he] using raw_energy⟩

def rawPairChecksOfAll (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (raw_pairPositive : decide (0<p.rho)=true)
    (raw_atomChain : chainCheck 1 4 (p.atomCells.map (fun x => ⟨x.left,x.right⟩))=true)
    (raw_atomCells : p.atomCells.all (fun x => cellUBF (latticeAtomCell z d x) x.witness)=true)
    (raw_pairScalar : scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
      seRat (-4-c.Iup-2*c.theta-2*latticePW d c-latticePA d c p)])=true) : RawLatticePairChecks z d c p where
  rho := raw_pairPositive
  chain := raw_atomChain
  cell := List.all_eq_true.mp raw_atomCells
  lower := raw_pairScalar
#print axioms rawSetupChecksOfAll
#print axioms rawPairChecksOfAll
end CatalanCore.Li2.DecayCert
