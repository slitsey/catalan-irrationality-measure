module
public import Init.Data.Rat.Basic
public import CatalanCore.Cert.QuarterCompute.ModelCellCached
public import CatalanCore.Cert.QuarterCompute.FastTableData
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.FastNode
open CatalanCore.Cert.QuarterCompute.ModelCell
open CatalanCore.Cert.QuarterCompute.DyadicInterval
abbrev Quad := Int × Int × Int × Int
abbrev QBox := Quad × Quad

def logLo (N : Nat) : Int :=
  let L := Nat.log2 N
  let m := N*2^8/2^L
  let e : Int := ((L : Int)-80)*(if 80 ≤ L then (FastTableData.lo 256 : Int) else (FastTableData.up 256 : Int))
  let c : Int := (((m+1)*2^(L+56)+N-1)/N : Nat)
  e+(FastTableData.lo (m-256+1) : Int)+2^64-c

def logUp (N : Nat) : Int :=
  let L := Nat.log2 N
  let m := N*2^8/2^L
  let e : Int := ((L : Int)-80)*(if 80 ≤ L then (FastTableData.up 256 : Int) else (FastTableData.lo 256 : Int))
  let c : Int := ((N*2^72+m*2^L-1)/(m*2^L) : Nat)
  e+(FastTableData.up (m-256) : Int)+c-2^64

def theta (vlo : Rat) : Rat :=
  let j := min (Rat.floor (vlo*256)).toNat 208
  (FastTableData.atan j : Rat)/2^64+
    (if j = 208 then 0 else (vlo-(j : Rat)/256)/(1+(((j : Rat)+1)/256)^2))

def thetaX (vlo : Rat) : Rat :=
  if (208 : Rat)/256 ≤ vlo then
    (FastTableData.atan 128 : Rat)/2^64+theta ((vlo-1/2)/(1+vlo/2))
  else theta vlo

def PILO : Rat := 314159265358979323846/10^20
def qmin (a b : Rat) : Rat := if a ≤ b then a else b
def qmax (a b : Rat) : Rat := if a ≤ b then b else a

def L1 (xlo yhi : Int) : Rat := (logUp (xlo*xlo+yhi*yhi).toNat : Rat)/2^64
def littleL (xhi ylo : Int) : Rat := (logLo ((2^40-xhi)^2+ylo^2).toNat : Rat)/2^64
def vlo (xlo ylo yhi : Int) : Rat :=
  (ylo : Rat)*2^40/((xlo : Rat)*xlo+yhi*yhi-xlo*2^40)

def boxLBg (Ls : Rat) (xlo xhi ylo yhi : Int) : Rat :=
  let l1 := L1 xlo yhi
  let Aup : Rat := (1/2)*qmax ((-(xhi : Rat)/2^40)*l1) ((-(xlo : Rat)/2^40)*l1)
  let l := littleL xhi ylo
  let Bup : Rat := -(1/2)*qmin ((((2 : Rat)^40-xhi)/2^40)*l)
    ((((2 : Rat)^40-xlo)/2^40)*l)
  let th := thetaX (vlo xlo ylo yhi)
  let Cup : Rat := -qmin ((ylo : Rat)/2^40*th) ((yhi : Rat)/2^40*th)
  Ls-(1+Aup+Bup+Cup)+(999/1000)*PILO*((ylo : Rat)/2^40)

def logThreeHalfLo : Rat := (logLo (3*2^79) : Rat)/2^64

def quarterBoxLB (epsilon Ls : Rat) (xl xh yl yh al ah bl bh : Int) : Rat :=
  (5/4)*Ls+(1/2)*boxLBg 0 xl xh yl yh+(3/4)*boxLBg 0 al ah bl bh+
    (3/4)*logThreeHalfLo+(1/1000-epsilon)*PILO*((yl : Rat)/2^40)

def boxGeom (b : QBox) : Prop :=
  b.1.2.1 < 0 ∧ b.1.1 ≤ b.1.2.1 ∧ 0 ≤ b.1.2.2.1 ∧
  b.2.2.1 < 0 ∧ b.2.1 ≤ b.2.2.1 ∧ 0 ≤ b.2.2.2.1 ∧
  (b.2.1 : Rat) ≤ 2*b.1.1/3 ∧ 2*(b.1.2.1 : Rat)/3 ≤ b.2.2.1 ∧
  (b.2.2.2.1 : Rat) ≤ 2*b.1.2.2.1/3 ∧ 2*(b.1.2.2.2 : Rat)/3 ≤ b.2.2.2.2
instance (b : QBox) : Decidable (boxGeom b) := by unfold boxGeom; infer_instance

def nodeOK (epsilon mp : Rat) (p : Model.Params)
    (cints : List Interval) (base : Int) (error : Nat) (b : QBox) : Bool :=
  decide (boxGeom b) &&
  decide (-H ≤ (vInterval p b.1.2.2.1 b.1.2.2.2).1 ∧
    (vInterval p b.1.2.2.1 b.1.2.2.2).2 ≤ H) &&
  decide (mp ≤ quarterBoxLB epsilon
    ((ModelCellCached.sigmaLower p cints base error b.1.2.2.1 b.1.2.2.2 : Int)/(2^48 : Rat))
    b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)
end CatalanCore.Cert.QuarterCompute.FastNode
