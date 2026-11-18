module
public import CatalanCore.Li2.DecayCert.Table
@[expose] public section
set_option Elab.async false
open Set
namespace CatalanCore.Li2.DecayCert

/-- Raw Boolean checker fields only; no potential/energy/measure inequality. -/
structure RawLatticeSetupChecks (z : ℚ) (d : LatticeInput) (c : LatticeSetup) where
  domain : decide (0 < |z| ∧ |z| < 1 ∧ 1≤c.cutoff ∧ d.Y≤c.cutoff)=true
  shape : latticeShapeCheck d=true
  density : datumCheck d.data c.density=true
  supportChain : chainCheck 0 d.Y (c.supportCells.map (fun x => ⟨x.left,x.right⟩))=true
  supportCell : ∀ x∈c.supportCells,cellUBF (fullLatticeCell z d x) x.witness=true
  rightChain : chainCheck d.Y c.cutoff (c.rightCells.map (fun x => ⟨x.left,x.right⟩))=true
  rightCell : ∀ x∈c.rightCells,rightCellCheck z d x=true
  tail : scalarUpperCheck (latticeTailExpr z d c) c.theta=true
  slope : scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0=true
  energy : ∃ e,latticeEnergyExpr d c.energy=some e ∧ scalarUpperCheck e c.Iup=true

theorem latticeSetupCheck_of_raw {z d c} (h : RawLatticeSetupChecks z d c) :
    latticeSetupCheck z d c=true := by
  rcases h.energy with ⟨e,he,hcap⟩
  simp only [latticeSetupCheck,Bool.and_eq_true,List.all_eq_true,he]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h.domain,h.shape⟩,h.density⟩,h.supportChain⟩,h.supportCell⟩,
    h.rightChain⟩,h.rightCell⟩,h.tail⟩,h.slope⟩,hcap⟩

def latticePackageOfRaw (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (h : RawLatticeSetupChecks z d c) : LatticePackage := ⟨z,d,c,latticeSetupCheck_of_raw h⟩

structure RawLatticePairChecks (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert) where
  rho : decide (0<p.rho)=true
  chain : chainCheck 1 4 (p.atomCells.map (fun x => ⟨x.left,x.right⟩))=true
  cell : ∀ x∈p.atomCells,cellUBF (latticeAtomCell z d x) x.witness=true
  lower : scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
    seRat (-4-c.Iup-2*c.theta-2*latticePW d c-latticePA d c p)])=true

theorem latticeCheck_of_raw {z d c p} (h : RawLatticePairChecks z d c p) :
    latticeCheck z d c p=true := by
  simp only [latticeCheck,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨h.rho,h.chain⟩,h.cell⟩,h.lower⟩

theorem allChecks_cons {α : Type*} (check : α → Bool) (x : α) (xs : List α)
    (hx : check x=true) (ht : xs.all check=true) : (x::xs).all check=true := by
  simp only [List.all_cons,hx,ht,Bool.and_self]

theorem chainCheck_cons_raw (a b : ℚ) (x : QInterval) (xs : List QInterval)
    (hl : x.left=a) (hlt : x.left<x.right) (hr : x.right≤b)
    (ht : chainCheck x.right b xs=true) : chainCheck a b (x::xs)=true := by
  simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hl,hlt,hr⟩,ht⟩
#print axioms latticeSetupCheck_of_raw
#print axioms latticeCheck_of_raw
#print axioms allChecks_cons
#print axioms chainCheck_cons_raw
end CatalanCore.Li2.DecayCert
