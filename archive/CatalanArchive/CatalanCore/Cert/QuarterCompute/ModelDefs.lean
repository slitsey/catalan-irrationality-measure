module
public import CatalanCore.Cert.QuarterCompute.Defs
public import CatalanCore.Cert.QuarterCompute.PolynomialOps
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial
structure Params where
  U : Nat
  X0 : Int
  Y0 : Int
  DX : Int
  DY : Int

def step (m : Params) : Int := (m.U / 2^40 : Nat)
def q0N (m : Params) (p : Pt) : Int :=
  (m.X0-p.1*step m)^2+(m.Y0-p.2.1*step m)^2+(m.U/2048 : Nat)^2
def an (m : Params) (p : Pt) : Int :=
  2*m.DX*(m.X0-p.1*step m)+2*m.DY*(m.Y0-p.2.1*step m)
def bn (m : Params) : Int := m.DX^2+m.DY^2

def validParams (m : Params) : Bool :=
  decide (0 < m.U ∧ m.U % 2^40 = 0 ∧ m.U % 2048 = 0)
def validJet (S : Nat) (m : Params) (p : Pt) (j : Jet) : Bool :=
  decide (0 < q0N m p ∧ j.2.2 = p.2.2 ∧
    j.1*q0N m p ≤ (S : Int)*an m p ∧ (S : Int)*an m p < (j.1+1)*q0N m p ∧
    j.2.1*q0N m p ≤ (S : Int)*bn m ∧ (S : Int)*bn m < (j.2.1+1)*q0N m p ∧
    j.1.natAbs+j.2.1.natAbs+2 < S)
def inputsOK (S : Nat) (m : Params) : List Pt → List Jet → Bool
  | [], [] => true
  | p::ps, j::js => validJet S m p j && inputsOK S m ps js
  | _, _ => false

def logUpS (N : Nat) : Int :=
  let L := Nat.log2 N
  let t := (N <<< 8) >>> L
  let e : Int := ((L : Int)-80)*(if 80 ≤ L then (tabUp 256 : Int) else (tabLo 256 : Int))
  let R : Int := (((N <<< 72)+(t <<< L)-1)/(t <<< L) : Nat)
  e+(tabUp (t-256) : Int)+R-2^64

def centreArg (m : Params) (p : Pt) : Nat :=
  ((q0N m p).toNat*2^80+m.U^2-1)/m.U^2
def baseSum (m : Params) : List Pt → Int
  | [] => 0
  | p::ps => (p.2.2 : Int)*logUpS (centreArg m p)+baseSum m ps

def ratioNumerator (j : Jet) : Nat := j.1.natAbs+j.2.1.natAbs+2
def errorCeil (S : Nat) (j : Jet) : Nat :=
  let r := ratioNumerator j
  let den := S^15*(S-r)
  (j.2.2*2^31*(r^16+2*S^15)+den-1)/den
def errorSum (S : Nat) : List Jet → Nat
  | [] => 0
  | j::js => errorCeil S j+errorSum S js
end CatalanCore.Cert.QuarterCompute.Model