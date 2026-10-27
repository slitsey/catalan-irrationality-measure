import Lean
import CatalanMeasure.CellCert.RawInts
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 50
namespace CatalanCore.Uniform.Decay.Optimization.EnergyPrecision
-- Arithmetic benchmark only: analytic/model-transfer soundness is not asserted.
def scale : Nat := 100000000000000000000000000000000000000000000000039
def seriesLoop (alt : Bool) (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Int → Int
  | 0, _, _, _, acc => acc
  | n+1, p, q, k, acc =>
    let t : Int := (scale * p / (q * (2*k+1)) : Nat)
    seriesLoop alt a2 b2 n (p*a2) (q*b2) (k+1)
      (acc + if alt && k % 2 == 1 then -t else t)
def series (alt : Bool) (a b : Nat) : Int := seriesLoop alt (a*a) (b*b) 96 a b 0 0
def log2Literal : Int := 69314718055994530941723212145817656807550013436000
def piLiteral : Int := 314159265358979323846264338327950288419716939937608
theorem constants_check : 2 * series false 1 3 = log2Literal ∧
    16 * series true 1 5 - 4 * series true 1 239 = piLiteral := by decide +kernel
abbrev Input := Nat × Int × Nat × Int
abbrev Expression := Int × Nat × List (Nat × Int × Nat)
def evalInput (input : Input) : Option (Int × Nat) :=
  let (kind, n, d, m) := input
  if d == 0 then none else
  if kind == 0 then some (piLiteral, 3000) else
  if kind == 1 then
    let (a,b) := if 0 ≤ m then (n.natAbs, d * 2^m.toNat)
                 else (n.natAbs * 2^(-m).toNat, d)
    if 0 < n && b ≤ a && a ≤ 2*b then
      some (2 * series false (a-b) (a+b) + m*log2Literal, 200*(1+m.natAbs))
    else none
  else if kind == 2 then
    let neg := n < 0
    let inv := d < n.natAbs
    let (a,b) := if inv then (d,n.natAbs) else (n.natAbs,d)
    let (v,e) : Int × Nat := if b < 2*a then
      (piLiteral / 4 - series true (b-a) (b+a), 900)
      else (series true a b, 100)
    let (v,e) := if inv then (piLiteral / 2-v,e+1700) else (v,e)
    some ((if neg then -v else v),e)
  else none

def evalInputs : List Input → Option (List (Int × Nat))
  | [] => some []
  | x::xs => do
    let v ← evalInput x
    let vs ← evalInputs xs
    some (v::vs)
def evalExpression (table : List (Int × Nat)) (x : Expression) : Int × Nat × Bool :=
  let (num,den,terms) := x
  terms.foldl (fun (v,err,ok) (idx,n,d) =>
    let (tv,te) := table.getD idx (0,0)
    (v + n*tv/(d : Int), err + (n.natAbs*te+d-1)/d+1,
      ok && decide (idx < table.length) && decide (0 < d)))
    (num*(scale : Int)/(den : Int),1,decide (0 < den))
def checkRows (table : List (Int × Nat)) : List Expression → List (Int × Int) → Bool
  | [], [] => true
  | x::xs, (lo,hi)::bs =>
    let (v,e,ok) := evalExpression table x
    ok && decide (lo ≤ v-(e : Int)) && decide (v+(e : Int) ≤ hi) && checkRows table xs bs
  | _,_ => false
def check (ins : List Input) (xs : List Expression) (bs : List (Int × Int)) : Bool :=
  match evalInputs ins with
  | none => false
  | some table => checkRows table xs bs

def inputTape : List Int → List Input
  | k::n::d::m::xs => (k.toNat,n,d.toNat,m)::inputTape xs
  | _ => []
def termTape : List Int → List (Nat × Int × Nat)
  | i::n::d::xs => (i.toNat,n,d.toNat)::termTape xs
  | _ => []
def valueTape : List Int → List (Int × Nat)
  | v::e::xs => (v,e.toNat)::valueTape xs
  | _ => []
theorem evalInputs_cons {x xs v vs} (h : evalInput x = some v)
    (hs : evalInputs xs = some vs) : evalInputs (x::xs) = some (v::vs) := by
  simp only [evalInputs, h, hs]
  rfl

end CatalanCore.Uniform.Decay.Optimization.EnergyPrecision
