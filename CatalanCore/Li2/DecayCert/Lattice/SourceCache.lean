module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.NativeAll
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
namespace CatalanCore.Li2.DecayCert.LatticeCache
open LatticeGate
structure SourceTable where
  density : List ℚ
  quotient : List ℚ
  own : List ℚ

def SourceTable.Correct (s : SourceTable) (d : QSegment) : Prop :=
  s.density=qDensityCoeffs d ∧ s.quotient=qQuotDensityCoeffs d ∧ s.own=qOwnCoeffs d

def canonicalSourceTable (d : QSegment) : SourceTable :=
  ⟨qDensityCoeffs d,qQuotDensityCoeffs d,qOwnCoeffs d⟩

def twoSourceTables (d0 : QSegment) (s0 : SourceTable) (d1 : QSegment) (s1 : SourceTable)
    (d : QSegment) : SourceTable :=
  if d=d0 then s0 else if d=d1 then s1 else canonicalSourceTable d

theorem twoSourceTables_correct (d0 : QSegment) (s0 : SourceTable) (h0 : s0.Correct d0)
    (d1 : QSegment) (s1 : SourceTable) (h1 : s1.Correct d1) (d : QSegment) :
    (twoSourceTables d0 s0 d1 s1 d).Correct d := by
  by_cases h : d=d0
  · subst d
    simpa only [twoSourceTables,ite_true] using h0
  · by_cases h' : d=d1
    · subst d
      simpa only [twoSourceTables,h,ite_false,ite_true] using h1
    · simp [twoSourceTables,h,h',SourceTable.Correct,canonicalSourceTable]
def ownCompileCached (table : SourceTable) (d : QSegment) (p e : CQ) (lo hi : ℚ) (Jord terms : ℕ) : Option CompiledModel :=
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  if cqSq d.half ≠ 0 ∧ x.2=0 ∧ (γ.2=0 ∨ (lo=0 ∧ hi=0)) ∧ lo ≤ hi ∧
      -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 ∧
      -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1 then
    let pown := table.own
    let rt := max |lo| |hi|
    let coeff := (List.range (Jord+1)).map (fun j : ℕ =>
      let q := (qShiftList pown x γ j).1
      if j=0 then seAdd (seRat q)
        (seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))) else seRat q)
    some ⟨coeff,seRat ((List.range (qListDegree pown+1)).map (fun j : ℕ =>
      if Jord < j then |(qShiftList pown x γ j).1| *rt^j else 0)).sum⟩
  else none

def segCoeffCached (table : SourceTable) (d : QSegment) (φ e : CQ) (j : ℕ) : CQ :=
  let ψ := cqInv φ
  let ζ := cqScale (1/2) (cqAdd φ ψ)
  let q := cqScale (1/2) (cqSub φ ψ)
  let γ := cqDiv e d.half
  if j=0 then (0,0) else
    let n := j-1
    let conv := cqSum ((List.range (n+1)).map (fun i : ℕ =>
      cqMul (qShiftList (table.density) ζ γ i) (yPair ζ γ q (n-i)).2))
    cqScale (1/(j:ℚ)) (cqMul γ (cqSub conv (qShiftList (table.quotient) ζ γ n)))


def segDiscCompileCached (table : SourceTable) (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) : Option CompiledModel :=
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
      (k+1:ℚ)*cqL1 (segCoeffCached table d w.phi e (k+1))*(rt+δ)^k)).sum
    some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
      if j=0 then segConstant w.terms d w.phi else seRat (segCoeffCached table d w.phi e j).1),
      seAdd (seScale (ρ^(w.order+1)/(1-ρ)) Mc) (seRat displacement)⟩
  else none


def compileCached (tables : QSegment→SourceTable) (lo hi : ℚ) : CellExpr → ModelWitness → Option CompiledModel
  | .constant e, .simple => some ⟨[e],seRat 0⟩
  | .variable, .simple => some ⟨[seRat 0,seRat 1],seRat 0⟩
  | .linear a b, .simple => some ⟨[a,b],seRat 0⟩
  | .poly p, .order J =>
      let rt := max |lo| |hi|
      some ⟨(List.range (J+1)).map (fun j : ℕ => seRat (coeffQ p j)),
        seRat (((List.range p.length).map (fun j : ℕ => if J < j then |coeffQ p j| *rt^j else 0)).sum)⟩
  | .add a b, .add wa wb => do
      let ma ← compileCached tables lo hi a wa
      let mb ← compileCached tables lo hi b wb
      pure ⟨combineCoeffs ma.coeff mb.coeff,seAdd ma.error mb.error⟩
  | .scale c a, .scale wa => do
      let ma ← compileCached tables lo hi a wa
      pure ⟨ma.coeff.map (seScale c),seScale |c| ma.error⟩
  | .segment d p e, .segOwn J n => ownCompileCached (tables d) d p e lo hi J n
  | .segment d p e, .segDisc w => segDiscCompileCached (tables d) d p e (max |lo| |hi|) w
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


theorem ownCompileCached_eq (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (d : QSegment) (p e : CQ) (lo hi : ℚ) (J terms : ℕ) :
    ownCompileCached (tables d) d p e lo hi J terms=ownCompileFast d p e lo hi J terms := by
  simp only [ownCompileCached,ownCompileFast,(hc d).2.2]

theorem segCoeffCached_eq (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (d : QSegment) (phi e : CQ) (j : ℕ) :
    segCoeffCached (tables d) d phi e j=segCoeffList d phi e j := by
  simp only [segCoeffCached,segCoeffList,(hc d).1,(hc d).2.1]

theorem segDiscCompileCached_eq (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) :
    segDiscCompileCached (tables d) d p e rt w=segDiscCompileList d p e rt w := by
  simp only [segDiscCompileCached,segDiscCompileList,segCoeffCached_eq tables hc]

theorem compileCached_eq (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) :
    compileCached tables lo hi e w=compileAllList lo hi e w := by
  induction e generalizing w <;> cases w <;>
    simp_all [compileCached,compileAllList,ownCompileCached_eq tables hc,segDiscCompileCached_eq tables hc]

theorem compileCached_original (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) :
    compileCached tables lo hi e w=compileModel lo hi e w :=
  (compileCached_eq tables hc lo hi e w).trans (compileAllList_eq lo hi e w)

theorem compileCached_literal (tables : QSegment→SourceTable) (hc : ∀d,(tables d).Correct d)
    (lo hi : ℚ) (e : CellExpr) (w : ModelWitness) (literal : CompiledModel)
    (hlit : compileCached tables lo hi e w=some literal) :
    compileModel lo hi e w=some literal := by
  rwa [←compileCached_original tables hc lo hi e w]
#print axioms twoSourceTables_correct
#print axioms compileCached_original
#print axioms compileCached_literal
end CatalanCore.Li2.DecayCert.LatticeCache
