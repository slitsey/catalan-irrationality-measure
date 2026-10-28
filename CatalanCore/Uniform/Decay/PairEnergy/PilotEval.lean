import CatalanCore.Uniform.Decay.PairEnergy.Oracle
import CatalanCore.Uniform.Decay.Cert.PilotSevenths
set_option Elab.async false
open CatalanCore.Uniform.Decay.PairEnergy CatalanCore.Uniform.Decay.Cert.Pilot CatalanCore.Uniform.Decay.Cert

def toF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den
def showPair (i j : Nat) : IO Unit := do
  match sevSegs[i]?, sevSegs[j]? with
  | some s1, some s2 =>
    let P := mkPair s1 s2
    IO.println s!"PAIR {i} {j} relOk={decide (P.rel = QC.zero)} ub={(pairUb P).map toF}"
  | _, _ => IO.println "missing"
#eval show IO Unit from do
  for (i,j) in [(0,0),(0,1),(0,5),(5,6),(5,5),(5,7),(7,8),(0,21),(21,21),(5,21),(7,22),(19,20)] do
    showPair i j

def qs (q : ℚ) : String := s!"{q.num}/{q.den}"
#eval show IO Unit from do
  for s in sevSegs do
    IO.println s!"SEG {qs s.ax} {qs s.ay} {qs s.bx} {qs s.byy} {String.intercalate " " (s.coef.map qs)}"

def capSeg : Seg := { ax := -273/2000, ay := 0, bx := 0, byy := 0, coef := [1], M := 1, Lq := 273/2000, tau := 0 }
#eval show IO Unit from do
  for i in [0,4,5,6,7,9,12,20] do
    let s := sevSegs.getD i capSeg
    let P := mkPair s capSeg
    IO.println s!"CAP {i} relOk={decide (P.rel = QC.zero)} ub={(pairUb P).map toF}"
