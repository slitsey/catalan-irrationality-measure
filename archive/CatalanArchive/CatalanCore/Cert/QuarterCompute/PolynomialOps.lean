module
public import CatalanCore.Cert.QuarterCompute.Polynomial
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.Polynomial

def add : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (a : Int) (cs : List Int) : List Int := cs.map (a*·)

def quad (a b : Int) : List Int → List Int
  | [] => []
  | c::cs => add (0::scale a (c::cs)) (0::0::scale b (c::cs))

def compose (a b : Int) : List Int → List Int
  | [] => []
  | c::cs => add [c] (quad a b (compose a b cs))

def mass : List Int → Nat
  | [] => 0
  | c::cs => c.natAbs+mass cs

def evalNat (x : Nat) : List Int → Nat
  | [] => 0
  | c::cs => c.natAbs+x*evalNat x cs

abbrev Jet := Int × Int × Nat

def jetCoeffs (factors : List Int) (p : Jet) : List Int :=
  scale (p.2.2 : Int) (compose p.1 p.2.1 factors)

def allCoeffs (factors : List Int) : List Jet → List Int
  | [] => []
  | p::ps => add (jetCoeffs factors p) (allCoeffs factors ps)

def sumWeights : List Jet → Nat
  | [] => 0
  | p::ps => p.2.2+sumWeights ps

def packedSum (factors : List Int) (B : Int) : List Jet → Int
  | [] => 0
  | p::ps => (p.2.2 : Int)*eval (p.1*B+p.2.1*B^2) factors+packedSum factors B ps
end CatalanCore.Cert.QuarterCompute.Polynomial