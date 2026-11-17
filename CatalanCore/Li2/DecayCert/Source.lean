module
public import CatalanCore.Li2.DecayCert.Arithmetic
public import CatalanCore.Li2.DecayCert.Segment
public import CatalanCore.Li2.DecayCert.RealCells.Elementary
public import CatalanMeasure.GenD.Signed.LogEval
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
abbrev CQ := ℚ×ℚ
def cqAdd (a b : CQ) : CQ := (a.1+b.1,a.2+b.2)
def cqNeg (a : CQ) : CQ := (-a.1,-a.2)
def cqSub (a b : CQ) : CQ := cqAdd a (cqNeg b)
def cqMul (a b : CQ) : CQ := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def cqSq (a : CQ) : ℚ := a.1^2+a.2^2
def cqInv (a : CQ) : CQ := (a.1/cqSq a,-a.2/cqSq a)
def cqDiv (a b : CQ) : CQ := cqMul a (cqInv b)
def cqScale (q : ℚ) (a : CQ) : CQ := (q*a.1,q*a.2)
def cqPow (a : CQ) : ℕ → CQ | 0 => (1,0) | n+1 => cqMul a (cqPow a n)
def cqL1 (a : CQ) : ℚ := |a.1|+|a.2|
noncomputable def cqReal (a : CQ) : ℂ := (a.1:ℂ)+(a.2:ℂ)*Complex.I

structure QSegment where
  mid : CQ
  half : CQ
  coeff : List ℚ
  deriving DecidableEq
def QSegment.c (d : QSegment) (k : ℕ) : ℚ := d.coeff[k]?.getD 0
noncomputable def QSegment.measure (d : QSegment) : Measure ℂ :=
  CatalanCore.Tools.Joukowski.segMeasure (cqReal d.mid) (cqReal d.half) (fun k => (d.c k:ℝ)) (d.coeff.length-1)
def QSegment.conj (d : QSegment) : QSegment :=
  ⟨(d.mid.1,-d.mid.2),(d.half.1,-d.half.2),d.coeff⟩
noncomputable def QSegment.density (d : QSegment) : ℚ[X] :=
  ∑ k ∈ Finset.range d.coeff.length, Polynomial.C (d.c k)*Polynomial.Chebyshev.T ℚ (k:ℤ)
noncomputable def QSegment.quotDensity (d : QSegment) : ℚ[X] :=
  ∑ k ∈ Finset.range (d.coeff.length-1),
    Polynomial.C (d.c (k+1))*Polynomial.Chebyshev.U ℚ (k:ℤ)
noncomputable def QSegment.ownPolyQ (d : QSegment) : ℚ[X] :=
  -∑ k ∈ Finset.range (d.coeff.length-1),
    Polynomial.C (d.c (k+1)/(k+1:ℕ))*Polynomial.Chebyshev.T ℚ ((k+1:ℕ):ℤ)

abbrev QBox := ℚ×ℚ
def boxSingleton (q : ℚ) : QBox := (q,q)
def boxAdd (a b : QBox) : QBox := (a.1+b.1,a.2+b.2)
def boxNeg (a : QBox) : QBox := (-a.2,-a.1)
def boxMul (a b : QBox) : QBox :=
  let xs := [a.1*b.1,a.1*b.2,a.2*b.1,a.2*b.2]
  (xs.foldl min (a.1*b.1),xs.foldl max (a.1*b.1))
def boxInv (a : QBox) : Option QBox :=
  if 0 < a.1 ∨ a.2 < 0 then some (a.2⁻¹,a.1⁻¹) else none
def boxAbs (a : QBox) : QBox :=
  (if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0 else min |a.1| |a.2|, max |a.1| |a.2|)
def boxEnc (v e : ℚ) : Option QBox := if 0 ≤ e then some (v-e,v+e) else none

inductive ScalarExpr
  | rat : ℚ → ScalarExpr
  | add : ScalarExpr → ScalarExpr → ScalarExpr
  | neg : ScalarExpr → ScalarExpr
  | mul : ScalarExpr → ScalarExpr → ScalarExpr
  | inv : ScalarExpr → ScalarExpr
  | abs : ScalarExpr → ScalarExpr
  | log : ℕ → ℚ → ScalarExpr
  | arg : ℕ → CQ → ScalarExpr
  | pi : ScalarExpr
  | logE : ℕ → ScalarExpr → ScalarExpr
  | argE : ℕ → ScalarExpr → ScalarExpr → ScalarExpr
  | atan : ℕ → ℚ → ScalarExpr
  | sqrt : ScalarExpr → ℚ → ℚ → ScalarExpr
  deriving DecidableEq
noncomputable def ScalarExpr.value : ScalarExpr → ℝ
  | .rat q => (q:ℝ)
  | .add a b => a.value+b.value
  | .neg a => -a.value
  | .mul a b => a.value*b.value
  | .inv a => a.value⁻¹
  | .abs a => |a.value|
  | .log _ q => Real.log (q:ℝ)
  | .arg _ q => Complex.arg (cqReal q)
  | .pi => Real.pi
  | .logE _ a => Real.log a.value
  | .argE _ a b => Complex.arg ((a.value:ℂ)+(b.value:ℂ)*Complex.I)
  | .atan _ q => Real.arctan (q:ℝ)
  | .sqrt a _ _ => Real.sqrt a.value

def argBox (n : ℕ) (A B : QBox) : Option QBox :=
  if B.1=0 ∧ B.2=0 ∧ A.2 < 0 then boxEnc (4*CatalanMeasure.GenD.Signed.LogEval.PI4) (4*CatalanMeasure.GenD.Signed.LogEval.PI4E)
  else if 0 < A.1 ∨ 0 < B.1 ∨ B.2 < 0 then do
    let bounds ← [(A.1,B.1),(A.1,B.2),(A.2,B.1),(A.2,B.2)].mapM (fun p => do
      let (v,e) ← CatalanMeasure.GenD.Signed.LogEval.argQ n p.1 p.2
      boxEnc v e)
    pure ((bounds.map Prod.fst).foldl min ((bounds.headD (0,0)).1),
      (bounds.map Prod.snd).foldl max ((bounds.headD (0,0)).2))
  else none

def ScalarExpr.check : ScalarExpr → Option QBox
  | .rat q => some (q,q)
  | .add a b => do pure (boxAdd (← a.check) (← b.check))
  | .neg a => do pure (boxNeg (← a.check))
  | .mul a b => do pure (boxMul (← a.check) (← b.check))
  | .inv a => do boxInv (← a.check)
  | .abs a => do pure (boxAbs (← a.check))
  | .log n q => do let (v,e) ← CatalanMeasure.GenD.Signed.LogEval.logQ n q; boxEnc v e
  | .arg n q => do
      if cqSq q=0 then none else
        let (v,e) ← CatalanMeasure.GenD.Signed.LogEval.argQ n q.1 q.2
        boxEnc v e
  | .pi => boxEnc (4*CatalanMeasure.GenD.Signed.LogEval.PI4) (4*CatalanMeasure.GenD.Signed.LogEval.PI4E)
  | .logE n a => do
      let b ← a.check
      if 0 < b.1 then
        let (vl,el) ← CatalanMeasure.GenD.Signed.LogEval.logQ n b.1
        let (vr,er) ← CatalanMeasure.GenD.Signed.LogEval.logQ n b.2
        pure (vl-el,vr+er)
      else none
  | .argE n a b => do argBox n (← a.check) (← b.check)
  | .atan n q => do let (v,e) ← CatalanMeasure.GenD.Signed.LogEval.atanQ n q; boxEnc v e
  | .sqrt a lo hi => do
      let A ← a.check
      if 0 ≤ lo ∧ lo ≤ hi ∧ 0 ≤ A.1 ∧ lo^2 ≤ A.1 ∧ A.2 ≤ hi^2
        then some (lo,hi) else none

noncomputable def QSegment.parameterMeasure (s : QSegment) : Measure ℝ :=
  (CatalanCore.Zeta5.Potential.arc.withDensity (fun θ => ENNReal.ofReal
    (CatalanCore.Zeta5.Potential.chebF (fun k => (s.c k:ℝ))
      (s.coeff.length-1) (Real.cos θ)))).map Real.cos


def coeffQ (a : List ℚ) (j : ℕ) : ℚ := a[j]?.getD 0

inductive CellExpr
  | constant : ScalarExpr → CellExpr
  | variable : CellExpr
  | linear : ScalarExpr → ScalarExpr → CellExpr
  | add : CellExpr → CellExpr → CellExpr
  | scale : ℚ → CellExpr → CellExpr
  | poly : List ℚ → CellExpr
  | fre : CQ → CQ → CellExpr
  | xlog : ℚ → ℚ → CellExpr
  | logAffine : CQ → CQ → CellExpr
  | invPow : CQ → CQ → ℕ → CellExpr
  | segment : QSegment → CQ → CQ → CellExpr
  | ulog : CellExpr
  deriving DecidableEq
noncomputable def CellExpr.value : CellExpr → ℝ → ℝ
  | .constant e, _ => e.value
  | .variable, u => u
  | .linear a b, u => a.value+b.value*u
  | .add a b, u => a.value u+b.value u
  | .scale c a, u => (c:ℝ)*a.value u
  | .poly a, u => ∑ j ∈ Finset.range a.length, (coeffQ a j:ℝ)*u^j
  | .fre a b, u =>
      let w := cqReal a+cqReal b*(u:ℂ)
      (w*Complex.log w-w).re
  | .xlog a b, u => CatalanCore.Li2.DecayCert.xlog ((a:ℝ)+(b:ℝ)*u)
  | .logAffine a b, u => Real.log ‖cqReal a+cqReal b*(u:ℂ)‖
  | .invPow a b k, u => ((cqReal a+cqReal b*(u:ℂ))^(-(k:ℤ))).re
  | .segment d p e, u => P d.measure (cqReal p+cqReal e*(u:ℂ))
  | .ulog, u => CatalanCore.Li2.DecayCert.xlog u

structure CellInput where
  expr : CellExpr
  lo : ℚ
  hi : ℚ
  scale : ℤ
  deriving DecidableEq
noncomputable def cellFun (x : CellInput) : ℝ → ℝ := x.expr.value

abbrev SE := ScalarExpr
def seAdd := ScalarExpr.add
def seNeg := ScalarExpr.neg
def seMul := ScalarExpr.mul
def seRat := ScalarExpr.rat
def seScale (q : ℚ) (e : SE) : SE := seMul (seRat q) e
def seSub (a b : SE) : SE := seAdd a (seNeg b)
def seSum (xs : List SE) : SE := xs.foldl seAdd (seRat 0)
def seLogNorm (n : ℕ) (a : CQ) : SE := seScale (1/2) (.log n (cqSq a))
def seReMulLog (n : ℕ) (b a : CQ) : SE :=
  seSub (seScale b.1 (seLogNorm n a)) (seScale b.2 (.arg n a))
def cqSum (xs : List CQ) : CQ := xs.foldl cqAdd (0,0)
def cqGet (xs : List CQ) (j : ℕ) : CQ := xs[j]?.getD (0,0)
def seGet (xs : List SE) (j : ℕ) : SE := xs[j]?.getD (.rat 0)

def exprSum (xs : List CellExpr) : CellExpr := xs.foldl CellExpr.add (.constant (.rat 0))
def fieldExpr (terms : ℕ) (z : ℚ) (p e : CQ) : CellExpr :=
  let kap : ℚ := if 0 < z then 2 else 1
  exprSum [.scale 3 (.fre (cqAdd p (1,0)) e), .scale (-2) (.fre p e),
    .scale (-1) (.fre (cqAdd p (4,0)) e),
    .linear (seSub (seScale p.1 (.log terms |z|)) (seScale (kap*p.2) .pi))
      (seSub (seScale e.1 (.log terms |z|)) (seScale (kap*e.2) .pi))]
def WExpr (terms : ℕ) (z : ℚ) (segments : List QSegment) (p e : CQ) : CellExpr :=
  .add (fieldExpr terms z p e)
    (exprSum (segments.map (fun s => .scale 2 (.segment s p e))))
def atomExpr (terms : ℕ) (z : ℚ) (segments : List QSegment) (x dir : ℚ) : CellExpr :=
  exprSum [.scale 2 (.xlog x dir), .scale (-3) (.xlog (x-1) dir),
    .scale (-1) (.xlog (4-x) (-dir)),
    .linear (seAdd (.rat 1) (seScale (-x) (.log terms |z|)))
      (seScale (-dir) (.log terms |z|)),
    exprSum (segments.map (fun s => .scale 2 (.segment s (-x,0) (-dir,0))))]


end CatalanCore.Li2.DecayCert
