import CatalanCore.Uniform.Decay.Breakpoint.GenBp
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanCore.Uniform.Decay.Breakpoint.GenBp
open CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearFast CatalanCore.Uniform.Decay.PolyCells

def probe (ei : ℕ) (up : ℚ) (side : Bool) (L : ℚ) (n : ℕ) : String :=
  let e := edgesLit[ei]!
  let ulo := if side then up - L else up
  let uhi := if side then up else up + L
  let a := cqOf e.1
  let b := cqOf e.2
  let zc := edgeCentre a b ulo uhi
  let dd := CQ.sub b a
  let h := (uhi - ulo) / 2
  let p := bpPoint side zc dd h
  let d' := bpDir side dd
  let S := 2 * h
  let far := bpFar p theps
  let inc := bpInc p theps
  s!"far {far.length} inc {inc.length} aggSome {(aggEvalMF n p d' S far).isSome} incAggSome {(incAgg n d' S inc).isSome} incs {inc.map fun P => (incEval n P d' S).isSome} farEach {far.map fun P => (pieceEval2F n P p d' S).isSome}"

def probe2 (ei : ℕ) (up : ℚ) (side : Bool) (L : ℚ) (n : ℕ) (k : ℕ) : String :=
  let e := edgesLit[ei]!
  let ulo := if side then up - L else up
  let uhi := if side then up else up + L
  let a := cqOf e.1
  let b := cqOf e.2
  let zc := edgeCentre a b ulo uhi
  let dd := CQ.sub b a
  let h := (uhi - ulo) / 2
  let p := bpPoint side zc dd h
  let d' := bpDir side dd
  let S := 2 * h
  let P := (bpFar p theps).getD k ⟨0, [], ⟨0, 0⟩, ⟨0, 0⟩, 0, 0⟩
  let z0 := z0of P.A P.B p
  let ee := eof P.A P.B d'
  s!"A=({fl P.A.re},{fl P.A.im}) B=({fl P.B.re},{fl P.B.im}) deg={P.a.length} z0=({fl z0.re},{fl z0.im}) e=({fl ee.re},{fl ee.im}) side={sideOk (z0of P.A P.B p) (eof P.A P.B d') S} nsq0={decide (z0.nsq ≠ 0)} q0={decide (sqrtUp ((q0of z0 ee).nsq * S ^ 2) < 1)} q1={decide (sqrtUp ((q1of z0 ee).nsq * S ^ 2) < 1)} lh={(logHalf (CQ.sub P.B P.A)).isSome} l0={(logHalf (CQ.neg z0)).isSome} a0={(argEnc (CQ.neg z0)).isSome} l1={(logHalf (CQ.sub CQ.one z0)).isSome} a1={(argEnc (CQ.sub CQ.one z0)).isSome} len={decide (P.a.length - 1 + 2 ≤ n)}"

#eval probe2 1 0 false (1 / 100000) 8 5
#eval probe2 0 0 false (1 / 100000) 8 5

end CatalanCore.Uniform.Decay.Breakpoint.GenBp
