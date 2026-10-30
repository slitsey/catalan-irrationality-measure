import CatalanCore.Uniform.Decay.NearFast.Cell
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch: the same rounded cells with the OLD rule `cellOk'` (paired baseline for D12). -/

namespace CatalanCore.Uniform.Decay.NearFast.GenS
open CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearCells.Pilot CatalanCore.Uniform.Decay.Tools

def fl' (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30
def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"
def rb (q : ℚ) : ℚ := (⌊q * 3 ^ 40⌋ : ℤ) / (3 ^ 40 : ℚ)
def litB (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"

def edgeCellS (name : String) (y0 y1 : ℚ) : String :=
  let ylo := rb y0
  let yhi := rb y1
  let zc := edge0Center ylo yhi
  let h := (yhi - ylo) / 2
  match aggEvalM nPilot zc edge0Dir h sevWP with
  | some (C, F) =>
    let Fs := ceil18 F
    let lo := loOf (cellPoly C cpiP zc edge0Dir) h
    s!"theorem {name} : cellOk' nPilot sevWP (edge0Center ({litB ylo}) ({litB yhi})) edge0Dir ((({litB yhi}) - ({litB ylo})) / 2) Wp 4 cpiP ({litQ lo}) mpP {litL C} ({litQ Fs}) 50 51 = true := by decide +kernel -- margin {fl' (lo - Fs - modSum 4 Wp 50 51 sevWP - mpP)}"
  | none => s!"-- {name} none"

#eval IO.println (edgeCellS "oldA" (1/25600) (1/12800))
#eval IO.println (edgeCellS "oldG" (1/160) (11/1600))
#eval IO.println (edgeCellS "oldWideC" (1/1677721600) (1/6553600))
end CatalanCore.Uniform.Decay.NearFast.GenS
