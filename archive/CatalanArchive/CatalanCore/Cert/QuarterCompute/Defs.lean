module
public import CatalanLambda.Cert.Tables
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute
open CatalanLambda.Cert
abbrev Pt := Int × Int × Nat
def tabLo (j : Nat) : Nat := (TLO >>> (64*j)) % 2^64
def tabUp (j : Nat) : Nat := (TUP >>> (64*j)) % 2^64
def logLoS (N : Nat) : Int :=
  let L := Nat.log2 N
  let m := (N <<< 8) >>> L
  let e : Int := ((L : Int) - 80) * (if 80 ≤ L then (tabLo 256 : Int) else (tabUp 256 : Int))
  let c : Int := ((((m + 1) <<< (L + 56)) + N - 1) / N : Nat)
  e + (tabLo (m - 256 + 1) : Int) + 2 ^ 64 - c
def pointAt (pts : List Pt) (k : Nat) : Pt := pts.getD k (0,0,0)
def qII (p q : Pt) : Nat := (p.1-q.1).natAbs^2+(p.2.1-q.2.1).natAbs^2+2^58
def iRow (p : Pt) : List Pt → Int
  | [] => 0
  | q::qs => (q.2.2 : Int)*logLoS (qII p q)+iRow p qs
end CatalanCore.Cert.QuarterCompute
