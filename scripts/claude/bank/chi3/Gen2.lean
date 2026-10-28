import CatalanCore.Uniform.Bank.Common.Data.Chi3.Data
import CatalanCore.Uniform.Decay.PolyFull.Full

/-! B3b generator, part 2 (scratch): pair-energy upper bounds and the cap integral lower bound. -/

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PairEnergy

namespace B3b

def Dc : SplineData := CatalanCore.Uniform.Bank.Common.Data.Chi3.data
def RP : List (ℚ × ℚ × ℚ) := [(1, 0, 1), (1 / 2, 1, 3 / 2)]

def ceilG (x : ℚ) (g : ℕ) : ℚ := ((x * g).ceil : ℤ) / (g : ℚ)
def floorG (x : ℚ) (g : ℕ) : ℚ := ((x * g).floor : ℤ) / (g : ℚ)

end B3b

open B3b in
def main (args : List String) : IO Unit := do
  match args with
  | ["E", k, n] =>
    let kk := k.toNat!; let nn := n.toNat!
    for i in List.range Dc.n do
      if i % nn == kk then
        for j in List.range Dc.n do
          match Dc.segs[i]?, Dc.segs[j]? with
          | some s1, some s2 =>
            let P := mkPair s1 s2
            let ok := decide (P.rel = QC.zero) && decide (QC.sub P.B1 P.A1 ≠ QC.zero) &&
              decide (QC.sub P.B2 P.A2 ≠ QC.zero)
            match pairUb P with
            | some u =>
              let e := ceilG u (10 ^ 20)
              IO.println s!"E {i} {j} {e.num} {e.den} {ok}"
            | none => IO.println s!"FAIL {i} {j} none"
          | _, _ => IO.println s!"FAIL {i} {j} idx"
  | ["G"] =>
    let a := listUb (fun j : Fin Dc.n => pairBound (capSegOf Dc.r0) (negSeg (Dc.seg j))) (List.finRange Dc.n)
    let b := listUb (fun p => pairBound (capSegOf Dc.r0) (pieceSeg p)) (RP ++ RP)
    match a, b with
    | some a, some b =>
      let g := Dc.Mq * Dc.r0 * (-a) - Dc.r0 * b / 2
      let G := floorG g (10 ^ 18)
      IO.println s!"G {G.num} {G.den} {decide (G ≤ g)}"
    | _, _ => IO.println "FAIL G"
  | _ => IO.eprintln "usage"
