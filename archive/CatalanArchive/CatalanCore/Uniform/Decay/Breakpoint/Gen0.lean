import CatalanCore.Uniform.Bank.Chi3.Tube.Top
import CatalanCore.Uniform.Decay.Breakpoint.Cell
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch (D14): list the Chi3 tube cells and the breakpoints on each edge. Not part of the library. -/

namespace CatalanCore.Uniform.Decay.Breakpoint.Gen0
open CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyCells

def fl (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30

def tag : CellKind2 → String
  | .jetF n _ _ _ => s!"J{n}"
  | .mixF n _ _ _ _ _ _ _ => s!"M{n}"
  | .far => "F"

def onEdge (e : Pt × Pt) (x : CQ) : Option ℚ :=
  let a := cqOf e.1
  let b := cqOf e.2
  let d := CQ.sub b a
  let u := if d.re ≠ 0 then (x.re - a.re) / d.re else (x.im - a.im) / d.im
  if x.re = a.re + u * d.re ∧ x.im = a.im + u * d.im ∧ 0 ≤ u ∧ u ≤ 1 then some u else none

def bps (e : Pt × Pt) : List ℚ :=
  (((cellPieces Dn nuC).flatMap fun P => [onEdge e P.A, onEdge e P.B]).filterMap id).eraseDups

#eval (edgesLit.map fun e => (bps e).map fl)
#eval (List.range 8).map fun i => ((tubeC.getD i []).map fun c => s!"{fl c.ulo}~{fl c.uhi}:{tag c.kind}")
#eval (edgesLit.map fun e => ((cellPieces Dn nuC).filter fun P => (onEdge e P.A).isSome && (onEdge e P.B).isSome).length)

end CatalanCore.Uniform.Decay.Breakpoint.Gen0
