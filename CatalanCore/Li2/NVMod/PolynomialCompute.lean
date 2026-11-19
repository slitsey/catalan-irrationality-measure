module
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Nat.Factorial.Basic
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.NVMod.PolynomialCompute
def djStepZ : List ℤ→List ℤ→Option (List ℤ)
  | c0::c1::c2::cs,p0::p1::p2::ps=>
      let num:=c0*c2-c1*c1
      if p2≠0 ∧ num%p2=0 then
        match djStepZ (c1::c2::cs) (p1::p2::ps) with
        | some r=>some (num/p2::r)
        | none=>none
      else none
  | _,_=>some []
def djLoopZ : ℕ→List ℤ→List ℤ→Option ℤ
  | 0,_,cur=>cur.head?
  | f+1,prev,cur=>match djStepZ cur prev with
    | some nxt=>djLoopZ f cur nxt
    | none=>none
def djEvalZ (n : ℕ) (m : List ℤ) : Option ℤ :=
  if n=0 then some 1 else
    if m.length=2*n-1 then djLoopZ (n-1) (List.replicate (2*n+1) 1) m else none

structure Data where
  moments : List (List ℤ)
  u : List ℤ
  v : List ℤ
  k : List ℤ
  degree : ℕ
  bits : ℕ
  kBound : ℕ

def horner (x : ℤ) (xs : List ℤ) : ℤ := xs.foldr (fun c acc=>c+x*acc) 0

def determinantBound (n d p : ℕ) : ℕ := n.factorial*(d+1)^(n-1)*p^n

def residualBound (n p : ℕ) (C : Data) : ℕ :=
  (p+1)*p*determinantBound n C.degree p+(p+1)*p+1+p*C.kBound

def boundsCheck (n p : ℕ) (C : Data) : Bool :=
  decide (C.moments.length=2*n-1 ∧
    C.u.length≤p+1 ∧ C.v.length≤n*C.degree+1) &&
  C.moments.all (fun xs=>decide (xs.length≤C.degree+1) &&
    xs.all (fun c=>decide (|c|≤(p:ℤ)))) &&
  C.u.all (fun c=>decide (|c|≤(p:ℤ))) &&
  C.v.all (fun c=>decide (|c|≤(p:ℤ))) &&
  C.k.all (fun c=>decide (|c|≤(C.kBound:ℤ))) &&
  decide (residualBound n p C<2^C.bits)

def boundsCheckNat (n p : ℕ) (C : Data) : Bool :=
  decide (C.moments.length=2*n-1 ∧
    C.u.length≤p+1 ∧ C.v.length≤n*C.degree+1) &&
  C.moments.all (fun xs=>decide (xs.length≤C.degree+1) &&
    xs.all (fun c=>decide (c.natAbs≤p))) &&
  C.u.all (fun c=>decide (c.natAbs≤p)) &&
  C.v.all (fun c=>decide (c.natAbs≤p)) &&
  C.k.all (fun c=>decide (c.natAbs≤C.kBound)) &&
  decide (residualBound n p C<2^C.bits)

def arithmeticCheck (n p : ℕ) (C : Data) : Bool :=
  let x : ℤ:=2^C.bits
  match djEvalZ n (C.moments.map (horner x)) with
  | none=>false
  | some F=>decide (horner x C.u*F+horner x C.v*horner x (List.replicate (p-1) 1)=
      1+(p:ℤ)*horner x C.k)

#print axioms arithmeticCheck
end CatalanCore.Li2.NVMod.PolynomialCompute

