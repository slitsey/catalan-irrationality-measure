module
public import CatalanCore.Li2.DecayCert.Compile
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.LatticeGate
def ownCompileFast (d : QSegment) (p e : CQ) (lo hi : ℚ) (Jord terms : ℕ) : Option CompiledModel :=
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  if cqSq d.half ≠ 0 ∧ x.2=0 ∧ (γ.2=0 ∨ (lo=0 ∧ hi=0)) ∧ lo ≤ hi ∧
      -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 ∧
      -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1 then
    let pown := qOwnCoeffs d
    let rt := max |lo| |hi|
    let coeff := (List.range (Jord+1)).map (fun j : ℕ =>
      let q := (qShiftList pown x γ j).1
      if j=0 then seAdd (seRat q)
        (seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))) else seRat q)
    some ⟨coeff,seRat ((List.range (qListDegree pown+1)).map (fun j : ℕ =>
      if Jord < j then |(qShiftList pown x γ j).1| *rt^j else 0)).sum⟩
  else none

theorem ownCompileFast_eq (d : QSegment) (p e : CQ) (lo hi : ℚ) (Jord terms : ℕ) :
    ownCompileFast d p e lo hi Jord terms=ownCompile d p e lo hi Jord terms := by
  simp only [ownCompileFast,ownCompile,qShiftList_own,qListDegree_spec,qOwnCoeffs_spec]
#print axioms ownCompileFast_eq

noncomputable def compileFast (lo hi : ℚ) : CellExpr → ModelWitness → Option CompiledModel
  | .constant e, .simple => some ⟨[e],seRat 0⟩
  | .variable, .simple => some ⟨[seRat 0,seRat 1],seRat 0⟩
  | .linear a b, .simple => some ⟨[a,b],seRat 0⟩
  | .poly p, .order J =>
      let rt := max |lo| |hi|
      some ⟨(List.range (J+1)).map (fun j : ℕ => seRat (coeffQ p j)),
        seRat (((List.range p.length).map (fun j : ℕ => if J < j then |coeffQ p j| *rt^j else 0)).sum)⟩
  | .add a b, .add wa wb => do
      let ma ← compileFast lo hi a wa
      let mb ← compileFast lo hi b wb
      pure ⟨combineCoeffs ma.coeff mb.coeff,seAdd ma.error mb.error⟩
  | .scale c a, .scale wa => do
      let ma ← compileFast lo hi a wa
      pure ⟨ma.coeff.map (seScale c),seScale |c| ma.error⟩
  | .segment d p e, .segOwn J n => ownCompileFast d p e lo hi J n
  | .segment d p e, .segDisc w => segDiscCompile d p e (max |lo| |hi|) w
  | .ulog, .regular w =>
      if lo=0 ∧ 0 < hi then some (ulogCompile hi w.terms) else none
  | .xlog a b, .seeds terms =>
      if a=0 ∧ 0 < b ∧ lo=0 ∧ 0 < hi then
        let m := ulogCompile hi terms
        some ⟨combineCoeffs (m.coeff.map (seScale b))
          [seRat 0,seScale b (.log terms b)],seScale b m.error⟩
      else none
  | .fre a b, .seeds terms =>
      if cqSq a=0 ∧ lo=0 ∧ hi=0 then some ⟨[seRat 0],seRat 0⟩
      else if cqSq a=0 ∧ cqSq b ≠ 0 ∧ lo=0 ∧ 0 < hi then
        let m := ulogCompile hi terms
        some ⟨combineCoeffs (m.coeff.map (seScale b.1))
          [seRat 0,seSub (seReMulLog terms b b) (seRat b.1)],seScale |b.1| m.error⟩
      else none
  | src, .regular w => regularCompile src lo hi w
  | _, _ => none

theorem compileFast_eq (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) :
    compileFast lo hi e w=compileModel lo hi e w := by
  induction e generalizing w <;> cases w <;>
    simp only [compileFast,compileModel,ownCompileFast_eq, *]
#print axioms compileFast_eq
end CatalanCore.Li2.DecayCert.LatticeGate

