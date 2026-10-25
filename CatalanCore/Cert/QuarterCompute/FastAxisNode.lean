module
public import CatalanCore.Cert.QuarterCompute.FastNode
public import Init.Data.Nat.Sqrt
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.FastAxisNode
open CatalanCore.Cert.QuarterCompute.FastNode

def qmax4 (a b c d : Rat) : Rat := qmax (qmax a b) (qmax c d)
def lloQ (N : Nat) : Rat := (logLo N : Rat)/2^65
def lupQ (N : Nat) : Rat := (logUp N : Rat)/2^65

def F1A (xl xh : Int) : Rat := if xh = 0 then 0 else
  qmax4 (((-xh : Int) : Rat)/2^40*lloQ (xh*xh).toNat)
    (((-xh : Int) : Rat)/2^40*lupQ (xl*xl).toNat)
    (((-xl : Int) : Rat)/2^40*lloQ (xh*xh).toNat)
    (((-xl : Int) : Rat)/2^40*lupQ (xl*xl).toNat)
def F2A (xh : Int) : Rat := -(((2^40-xh : Int) : Rat)/2^40*lloQ ((2^40-xh)^2).toNat)
def utA (xl xh : Int) : Rat := 1+F1A xl xh+F2A xh

def tlogUB (t1 t2 : Int) : Rat :=
  if t1 = 0 then 2*(((Nat.sqrt (t2.toNat*2^40)+1 : Nat) : Rat)/2^40) else
    qmax4 ((t1 : Rat)/2^40*(-lupQ (t2*t2).toNat)) ((t1 : Rat)/2^40*(-lloQ (t1*t1).toNat))
      ((t2 : Rat)/2^40*(-lupQ (t2*t2).toNat)) ((t2 : Rat)/2^40*(-lloQ (t1*t1).toNat))
def utB (xl xh : Int) : Rat := 1+tlogUB xl xh+tlogUB (2^40-xh) (2^40-xl)
def axisUt (a b : Int) : Rat := if b ≤ 0 then utA a b else utB a b

def axisDomain (a b : Int) : Prop := a ≤ b ∧ ((-(2^40 : Int) ≤ a ∧ b ≤ 0) ∨ (0 ≤ a ∧ b ≤ 2^40))
instance (a b : Int) : Decidable (axisDomain a b) := by unfold axisDomain; infer_instance
def axisGeom (b : QBox) : Prop :=
  axisDomain b.1.1 b.1.2.1 ∧ axisDomain b.2.1 b.2.2.1 ∧
  b.1.2.2.1 = 0 ∧ b.1.2.2.2 = 0 ∧
  (b.2.1 : Rat) ≤ 2*b.1.1/3 ∧ 2*(b.1.2.1 : Rat)/3 ≤ b.2.2.1
instance (b : QBox) : Decidable (axisGeom b) := by unfold axisGeom; infer_instance

def quarterAxisLB (Ls u1 u2 : Rat) : Rat :=
  (5/4)*Ls-(1/2)*u1-(3/4)*u2+(3/4)*logThreeHalfLo
end CatalanCore.Cert.QuarterCompute.FastAxisNode
