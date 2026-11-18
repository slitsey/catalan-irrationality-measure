module
public import CatalanCore.Li2.DecayCert.RealCells
public import CatalanCore.Li2.DecayCert.Source.Sound
public import CatalanCore.Li2.DecayCert.PolynomialList
public import CatalanCore.Li2.DecayCert.SlitDistance
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section
def combineCoeffs (a b : List SE) : List SE :=
  (List.range (max a.length b.length)).map (fun j : ℕ => seAdd (seGet a j) (seGet b j))

-- Exact polynomial Taylor coefficients over Gaussian rationals.

def yPair (ζ γ q : CQ) : ℕ → CQ×CQ
  | 0 => ((0,0),cqInv q)
  | n+1 =>
      let v := yPair ζ γ q n
      let A := cqMul q q
      let B := cqScale 2 (cqMul ζ γ)
      let C := cqMul γ γ
      let next := cqScale (-(1/(n+1:ℚ))) (cqDiv
        (cqAdd (cqScale ((n:ℚ)+1/2) (cqMul B v.2))
          (cqScale (n:ℚ) (cqMul C v.1))) A)
      (v.2,next)

def segCoeff (d : QSegment) (φ e : CQ) (j : ℕ) : CQ :=
  let ψ := cqInv φ
  let ζ := cqScale (1/2) (cqAdd φ ψ)
  let q := cqScale (1/2) (cqSub φ ψ)
  let γ := cqDiv e d.half
  if j=0 then (0,0) else
    let n := j-1
    let conv := cqSum ((List.range (n+1)).map (fun i : ℕ =>
      cqMul (qShiftCoeff d.density ζ γ i) (yPair ζ γ q (n-i)).2))
    cqScale (1/(j:ℚ)) (cqMul γ (cqSub conv (qShiftCoeff d.quotDensity ζ γ n)))

def segConstant (terms : ℕ) (d : QSegment) (φ : CQ) : SE :=
  seSub (seScale (d.c 0)
    (seSub (seAdd (seLogNorm terms d.half) (seLogNorm terms φ)) (.log terms 2)))
    (seRat ((List.range (d.coeff.length-1)).map (fun k : ℕ =>
      d.c (k+1)*(cqPow (cqInv φ) (k+1)).1/(k+1:ℚ))).sum)

structure SegDiscWitness where
  phi : CQ
  order : ℕ
  terms : ℕ
  distanceLo : ℚ
  gammaHi : ℚ
  zetaHi : ℚ
  radius : ℚ
  phiHi : ℚ
  fraction : ℚ

structure RegularWitness where
  order : ℕ
  terms : ℕ
  normLo : ℚ
  normHi : ℚ
  directionHi : ℚ
  radius : ℚ

structure CompiledModel where
  coeff : List SE
  error : SE

inductive ModelWitness
  | simple : ModelWitness
  | seeds : ℕ → ModelWitness
  | order : ℕ → ModelWitness
  | regular : RegularWitness → ModelWitness
  | segOwn : ℕ → ℕ → ModelWitness
  | segDisc : SegDiscWitness → ModelWitness
  | add : ModelWitness → ModelWitness → ModelWitness
  | scale : ModelWitness → ModelWitness

def regularOK (a b : CQ) (rt : ℚ) (w : RegularWitness) : Bool :=
  decide (2 ≤ w.order ∧ 0 < w.normLo ∧ w.normLo ≤ w.normHi ∧
    w.normLo^2 ≤ cqSq a ∧ cqSq a ≤ w.normHi^2 ∧
    0 ≤ w.directionHi ∧ cqSq b ≤ w.directionHi^2 ∧
    0 ≤ rt ∧ w.directionHi*rt < w.normLo)

def segDiscOK (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) : Bool :=
  let ψ := cqInv w.phi
  let ζ := cqScale (1/2) (cqAdd w.phi ψ)
  let γ := cqDiv e d.half
  let center := cqAdd d.mid (cqMul d.half ζ)
  let δ := cqL1 (cqDiv (cqSub p center) e)
  decide (cqSq d.half ≠ 0 ∧ cqSq e ≠ 0 ∧ 1 < cqSq w.phi ∧
    0 < w.distanceLo ∧ w.distanceLo^2 ≤ slitDistSq ζ ∧
    0 ≤ w.gammaHi ∧ cqSq γ ≤ w.gammaHi^2 ∧
    0 ≤ w.zetaHi ∧ cqSq ζ ≤ w.zetaHi^2 ∧
    0 < w.radius ∧ 0 < w.fraction ∧ w.fraction < 1 ∧
    w.gammaHi*w.radius ≤ w.fraction*w.distanceLo ∧
    0 ≤ rt ∧ rt+δ < w.radius ∧
    1 ≤ w.phiHi ∧ w.zetaHi+w.gammaHi*w.radius ≤ w.phiHi ∧
    (w.zetaHi+w.gammaHi*w.radius)^2+1 ≤
      (w.phiHi-(w.zetaHi+w.gammaHi*w.radius))^2)

def segDiscCompile (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness) : Option CompiledModel :=
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
      (k+1:ℚ)*cqL1 (segCoeff d w.phi e (k+1))*(rt+δ)^k)).sum
    some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
      if j=0 then segConstant w.terms d w.phi else seRat (segCoeff d w.phi e j).1),
      seAdd (seScale (ρ^(w.order+1)/(1-ρ)) Mc) (seRat displacement)⟩
  else none

def ownCompile (d : QSegment) (p e : CQ) (lo hi : ℚ) (Jord terms : ℕ) : Option CompiledModel :=
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  if cqSq d.half ≠ 0 ∧ x.2=0 ∧ (γ.2=0 ∨ (lo=0 ∧ hi=0)) ∧ lo ≤ hi ∧
      -1 ≤ x.1+γ.1*lo ∧ x.1+γ.1*lo ≤ 1 ∧
      -1 ≤ x.1+γ.1*hi ∧ x.1+γ.1*hi ≤ 1 then
    let pown := d.ownPolyQ
    let rt := max |lo| |hi|
    let coeff := (List.range (Jord+1)).map (fun j : ℕ =>
      let q := (qShiftCoeff pown x γ j).1
      if j=0 then seAdd (seRat q)
        (seScale (d.c 0) (seSub (seLogNorm terms d.half) (.log terms 2))) else seRat q)
    some ⟨coeff,seRat ((List.range (pown.natDegree+1)).map (fun j : ℕ =>
      if Jord < j then |(qShiftCoeff pown x γ j).1| *rt^j else 0)).sum⟩
  else none

def regularCompile (src : CellExpr) (lo hi : ℚ) (w : RegularWitness) : Option CompiledModel :=
  let rt := max |lo| |hi|
  match src with
  | .fre a b =>
      if regularOK a b rt w && decide (0 ≤ a.1) then
        let ρ := w.directionHi*rt/w.normLo
        some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
          if j=0 then seSub (seReMulLog w.terms a a) (seRat a.1)
          else if j=1 then seReMulLog w.terms b a
          else seRat (cqScale ((-1:ℚ)^j/((j:ℚ)*(j-1)))
            (cqDiv (cqPow b j) (cqPow a (j-1)))).1),
          seRat (w.normHi*ρ^(w.order+1)/((w.order+1:ℚ)*w.order*(1-ρ)))⟩
      else none
  | .xlog a b =>
      if 2 ≤ w.order ∧ 0 < a ∧ lo ≤ hi ∧ |b| *rt < a then
        let ρ := |b| *rt/a
        some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
          if j=0 then seScale a (.log w.terms a)
          else if j=1 then seScale b (seAdd (.log w.terms a) (seRat 1))
          else seRat ((-1:ℚ)^j*b^j/((j:ℚ)*(j-1)*a^(j-1)))),
          seRat (a*ρ^(w.order+1)/((w.order+1:ℚ)*w.order*(1-ρ)))⟩
      else none
  | .logAffine a b =>
      if regularOK a b rt w then
        let ρ := w.directionHi*rt/w.normLo
        some ⟨(List.range (w.order+1)).map (fun j : ℕ =>
          if j=0 then seLogNorm w.terms a
          else seRat (cqScale ((-1:ℚ)^(j+1)/(j:ℚ)) (cqPow (cqDiv b a) j)).1),
          seRat (ρ^(w.order+1)/((w.order+1:ℚ)*(1-ρ)))⟩
      else none
  | .invPow a b k =>
      if k=0 then some ⟨[seRat 1],seRat 0⟩ else
      if regularOK a b rt w && decide (rt < w.radius ∧ w.directionHi*w.radius < w.normLo) then
        let ρ := rt/w.radius
        some ⟨(List.range (w.order+1)).map (fun j : ℕ => seRat
          (cqScale ((-1:ℚ)^j*((k+j-1).choose j:ℚ))
            (cqDiv (cqPow b j) (cqPow a (k+j)))).1),
          seRat ((w.normLo-w.directionHi*w.radius)^(-(k:ℤ))*ρ^(w.order+1)/(1-ρ))⟩
      else none
  | _ => none

def ulogCompile (hi : ℚ) (terms : ℕ) : CompiledModel :=
  let t := hi/2
  ⟨[seRat (-t/2),seScale (1/2)
      (seAdd (seAdd (.log terms t) (seRat 1)) (.log terms hi))],seRat (hi/4)⟩

def compileModel (lo hi : ℚ) : CellExpr → ModelWitness → Option CompiledModel
  | .constant e, .simple => some ⟨[e],seRat 0⟩
  | .variable, .simple => some ⟨[seRat 0,seRat 1],seRat 0⟩
  | .linear a b, .simple => some ⟨[a,b],seRat 0⟩
  | .poly p, .order J =>
      let rt := max |lo| |hi|
      some ⟨(List.range (J+1)).map (fun j : ℕ => seRat (coeffQ p j)),
        seRat (((List.range p.length).map (fun j : ℕ => if J < j then |coeffQ p j| *rt^j else 0)).sum)⟩
  | .add a b, .add wa wb => do
      let ma ← compileModel lo hi a wa
      let mb ← compileModel lo hi b wb
      pure ⟨combineCoeffs ma.coeff mb.coeff,seAdd ma.error mb.error⟩
  | .scale c a, .scale wa => do
      let ma ← compileModel lo hi a wa
      pure ⟨ma.coeff.map (seScale c),seScale |c| ma.error⟩
  | .segment d p e, .segOwn J n => ownCompile d p e lo hi J n
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

def PositiveSources : CellExpr → Prop
  | .add a b => PositiveSources a ∧ PositiveSources b
  | .scale _ a => PositiveSources a
  | .segment d _ _ => ∀ x ∈ Icc (-1:ℝ) 1,
      0 ≤ CatalanCore.Zeta5.Potential.chebF (fun k : ℕ => (d.c k:ℝ)) (d.coeff.length-1) x
  | _ => True

structure CellWitness where
  model : ModelWitness
  coeff : List ℤ
  error : List ℤ
  remainder : ℚ
  lb : ℚ
  ub : ℚ

def gridCoeffs (S : ℤ) (w : CellWitness) : List ℚ :=
  w.coeff.map (fun a : ℤ => (a:ℚ)/(S:ℚ))

def coeffEnclosed (S : ℤ) (a e : ℤ) (b : QBox) : Bool :=
  decide (0 ≤ e ∧ ((a-e:ℤ):ℚ)/(S:ℚ) ≤ b.1 ∧ b.2 ≤ ((a+e:ℤ):ℚ)/(S:ℚ))

def coefficientCheck (S : ℤ) (m : CompiledModel) (w : CellWitness) : Bool :=
  decide (0 < S ∧ m.coeff.length=w.coeff.length ∧ w.error.length=w.coeff.length) &&
    ((List.range m.coeff.length).all (fun j : ℕ => match (seGet m.coeff j).check with
      | none => false
      | some b => coeffEnclosed S (getI w.coeff j) (getI w.error j) b))

def remainderCheck (S : ℤ) (rt : ℚ) (m : CompiledModel) (w : CellWitness) : Bool :=
  match m.error.check with
  | none => false
  | some b => decide (0 ≤ b.1 ∧ 0 ≤ w.remainder ∧
      b.2 + ((List.range w.error.length).map (fun j : ℕ =>
        (getI w.error j:ℚ)/(S:ℚ)*rt^j)).sum ≤ w.remainder)

def cellUBF (x : CellInput) (w : CellWitness) : Bool :=
  match compileModel x.lo x.hi x.expr w.model with
  | none => false
  | some m => decide (x.lo ≤ x.hi) && coefficientCheck x.scale m w &&
      remainderCheck x.scale (max |x.lo| |x.hi|) m w &&
      decide (polyUBQ (gridCoeffs x.scale w) x.lo x.hi+w.remainder ≤ w.ub ∧
        w.lb ≤ polyLBQ (gridCoeffs x.scale w) x.lo x.hi-w.remainder)

structure LineWitness where
  cell : CellWitness
  a : ℚ
  b : ℚ

def upperLine (co : List ℚ) (R err : ℚ) : ℚ×ℚ :=
  let c0 := coeffQ co 0
  let c1 := coeffQ co 1
  let c2 := coeffQ co 2
  let tail := err+((List.range co.length).map (fun j : ℕ =>
    if 3 ≤ j then |coeffQ co j| *R^j else 0)).sum
  (c0+tail+(if c2 < 0 then -c2*R^2/4 else 0),c1+c2*R)

def lineCellF (x : CellInput) (w : LineWitness) : Bool :=
  cellUBF x w.cell && decide (x.lo=0 ∧ 0 ≤ x.hi) &&
    let line := upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder
    decide (line.1 ≤ w.a ∧ line.1+line.2*x.hi ≤ w.a+w.b*x.hi)

def phi0Expr (p e : CQ) : CellExpr := exprSum
  [.scale 3 (.fre (cqAdd p (1,0)) e),.scale (-2) (.fre p e),.scale (-1) (.fre (cqAdd p (4,0)) e)]

theorem cqReal_re (a : CQ) : (cqReal a).re=(a.1:ℝ) := by simp [cqReal]

theorem cqReal_im (a : CQ) : (cqReal a).im=(a.2:ℝ) := by simp [cqReal]

theorem cqSq_eq_norm_sq (a : CQ) : (cqSq a:ℝ)=‖cqReal a‖^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply,cqReal_re,cqReal_im]
  simp [cqSq,pow_two]

theorem seRat_value (q : ℚ) : (seRat q).value=(q:ℝ) := rfl

theorem seAdd_value (a b : SE) : (seAdd a b).value=a.value+b.value := rfl

theorem seNeg_value (a : SE) : (seNeg a).value= -a.value := rfl

theorem seSub_value (a b : SE) : (seSub a b).value=a.value-b.value := rfl

theorem seScale_value (q : ℚ) (a : SE) : (seScale q a).value=(q:ℝ)*a.value := rfl

theorem seLogNorm_value (n : ℕ) (a : CQ) : (seLogNorm n a).value=Real.log ‖cqReal a‖ := by
  change ((1/2:ℚ):ℝ)*Real.log (cqSq a:ℝ)=_
  rw [cqSq_eq_norm_sq,Real.log_pow]
  push_cast
  ring

theorem seReMulLog_value (n : ℕ) (b a : CQ) :
    (seReMulLog n b a).value=(cqReal b*Complex.log (cqReal a)).re := by
  rw [seReMulLog,seSub_value,seScale_value,seScale_value,seLogNorm_value]
  simp only [Complex.mul_re,Complex.log_re,Complex.log_im,cqReal_re,cqReal_im,
    ScalarExpr.value]

#print axioms cqReal_re
#print axioms cqReal_im
#print axioms cqSq_eq_norm_sq
#print axioms seRat_value
#print axioms seAdd_value
#print axioms seNeg_value
#print axioms seSub_value
#print axioms seScale_value
#print axioms seLogNorm_value
#print axioms seReMulLog_value
end
end CatalanCore.Li2.DecayCert
