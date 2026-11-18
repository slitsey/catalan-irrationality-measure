module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Own
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
namespace CatalanCore.Li2.DecayCert.LatticeGate
def segCoeffList (d : QSegment) (φ e : CQ) (j : ℕ) : CQ :=
  let ψ := cqInv φ
  let ζ := cqScale (1/2) (cqAdd φ ψ)
  let q := cqScale (1/2) (cqSub φ ψ)
  let γ := cqDiv e d.half
  if j=0 then (0,0) else
    let n := j-1
    let conv := cqSum ((List.range (n+1)).map (fun i : ℕ =>
      cqMul (qShiftList (qDensityCoeffs d) ζ γ i) (yPair ζ γ q (n-i)).2))
    cqScale (1/(j:ℚ)) (cqMul γ (cqSub conv (qShiftList (qQuotDensityCoeffs d) ζ γ n)))


theorem segCoeffList_eq (d : QSegment) (phi e : CQ) (j : ℕ) :
    segCoeffList d phi e j=segCoeff d phi e j := by
  simp only [segCoeffList,segCoeff,qShiftList_density,qShiftList_quotDensity]
def segDiscCompileList (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) : Option CompiledModel :=
  if segDiscOK d p e rt w then
    let ζ := cqScale (1/2) (cqAdd w.phi (cqInv w.phi))
    let center := cqAdd d.mid (cqMul d.half ζ)
    let δ := cqL1 (cqDiv (cqSub p center) e)
    let ρ := (rt+δ)/w.radius
    let Mc := seAdd (seScale |d.c 0|
      (seAdd (.log w.terms w.phiHi)
        (seAdd (.log w.terms 2) (seAdd .pi (.log w.terms (1/(1-w.fraction)))))))
      (seRat ((List.range (d.coeff.length-1)).map (fun k : ℕ => |d.c (k+1)|/(k+1:ℚ))).sum)
    let displacement := δ*((List.range w.order).map (fun k : ℕ =>
      (k+1:ℚ)*cqL1 (segCoeffList d w.phi e (k+1))*(rt+δ)^k)).sum
    some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
      if j=0 then segConstant w.terms d w.phi else seRat (segCoeffList d w.phi e j).1),
      seAdd (seScale (ρ^(w.order+1)/(1-ρ)) Mc) (seRat displacement)⟩
  else none


theorem segDiscCompileList_eq (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) :
    segDiscCompileList d p e rt w=segDiscCompile d p e rt w := by
  simp only [segDiscCompileList,segDiscCompile,segCoeffList_eq]
def compileAllList (lo hi : ℚ) : CellExpr → ModelWitness → Option CompiledModel
  | .constant e, .simple => some ⟨[e],seRat 0⟩
  | .variable, .simple => some ⟨[seRat 0,seRat 1],seRat 0⟩
  | .linear a b, .simple => some ⟨[a,b],seRat 0⟩
  | .poly p, .order J =>
      let rt := max |lo| |hi|
      some ⟨(List.range (J+1)).map (fun j : ℕ => seRat (coeffQ p j)),
        seRat (((List.range p.length).map (fun j : ℕ => if J < j then |coeffQ p j| *rt^j else 0)).sum)⟩
  | .add a b, .add wa wb => do
      let ma ← compileAllList lo hi a wa
      let mb ← compileAllList lo hi b wb
      pure ⟨combineCoeffs ma.coeff mb.coeff,seAdd ma.error mb.error⟩
  | .scale c a, .scale wa => do
      let ma ← compileAllList lo hi a wa
      pure ⟨ma.coeff.map (seScale c),seScale |c| ma.error⟩
  | .segment d p e, .segOwn J n => ownCompileFast d p e lo hi J n
  | .segment d p e, .segDisc w => segDiscCompileList d p e (max |lo| |hi|) w
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


theorem compileAllList_eq (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) :
    compileAllList lo hi e w=compileModel lo hi e w := by
  induction e generalizing w <;> cases w <;>
    simp_all [compileAllList,compileModel,ownCompileFast_eq,segDiscCompileList_eq]
def cellUBFAllList (x : CellInput) (w : CellWitness) : Bool :=
  match compileAllList x.lo x.hi x.expr w.model with
  | none => false
  | some m => decide (x.lo ≤ x.hi) && coefficientCheck x.scale m w &&
      remainderCheck x.scale (max |x.lo| |x.hi|) m w &&
      decide (polyUBQ (gridCoeffs x.scale w) x.lo x.hi+w.remainder ≤ w.ub ∧
        w.lb ≤ polyLBQ (gridCoeffs x.scale w) x.lo x.hi-w.remainder)


theorem cellUBFAllList_eq (x : CellInput) (w : CellWitness) : cellUBFAllList x w=cellUBF x w := by
  simp only [cellUBFAllList,cellUBF,compileAllList_eq] <;>rfl
#print axioms segCoeffList_eq
#print axioms segDiscCompileList_eq
#print axioms compileAllList_eq
#print axioms cellUBFAllList_eq
end CatalanCore.Li2.DecayCert.LatticeGate
