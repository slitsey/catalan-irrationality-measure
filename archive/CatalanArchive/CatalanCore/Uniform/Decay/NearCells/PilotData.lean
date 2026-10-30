import CatalanCore.Uniform.Decay.NearCells.Rules
import CatalanCore.Uniform.Decay.Cert.PilotSevenths
set_option Elab.async false
set_option maxRecDepth 100000

/-! Pilot data (lane D6b): the sevenths trial, edge 0 of the polygon. -/

namespace CatalanCore.Uniform.Decay.NearCells.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot
  CatalanCore.Uniform.Decay.Tools

def wpOfSeg (w : ℚ) (sg : Seg) : WP :=
  ⟨w, sg.coef, ⟨sg.ax, sg.ay⟩, ⟨sg.bx, sg.byy⟩, sg.M, sg.Lq⟩

def nuWP : List WP :=
  [⟨-1, [1], ⟨0, 0⟩, ⟨1, 0⟩, 1, 1⟩, ⟨-1, [1 / 12], ⟨1, 0⟩, ⟨7 / 6, 0⟩, 1 / 12, 1 / 6⟩]

def sevWP : List WP := sevSegs.map (wpOfSeg (13 / 12)) ++ nuWP

/-- Edge 0 of the polygon: base `-r0`, direction `(lean0, 1)`; the cell is `y ∈ [ylo, yhi]`. -/
def edge0Center (ylo yhi : ℚ) : CQ :=
  ⟨-273 / 2000 + (-2521 / 5000) * ((ylo + yhi) / 2), (ylo + yhi) / 2⟩
def edge0Dir : CQ := ⟨-2521 / 5000, 1⟩

def nPilot : ℕ := 8
def Wp : ℚ := 1 / 1000000000000000
def cpiP : ℚ := (999 / 1000) * (3141592 / 1000000)

/-- Lower bound of the aggregated polynomial on the cell (rounded down on a 10^-18 grid). -/
def loOf (C : List ℚ) (h : ℚ) : ℚ :=
  let bs := (List.range nPilot).map fun k => bernK (affK (coeffs C) (nPilot - 1) (-h) (2 * h)) (nPilot - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)

def rf (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30

def mpP : ℚ := 5351328094624509 / 2500000000000000

def modP (ps : List WP) : ℚ := modSum 4 Wp 50 51 ps

def cellData (ylo yhi : ℚ) : Option (List ℚ × ℚ × ℚ × ℚ) :=
  let h := (yhi - ylo) / 2
  let zc := edge0Center ylo yhi
  match aggEval nPilot zc edge0Dir h sevWP with
  | some (C, F) =>
    let Fs : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
    some (C, loOf (cellPoly C cpiP zc edge0Dir) h, Fs, F)
  | none => none

def emit (name : String) (ylo yhi : ℚ) : String :=
  match cellData ylo yhi with
  | some (C, lo, Fs, F) =>
    let lst := String.intercalate ", " (C.map fun q => s!"(({q.num} : ℤ) : ℚ) / {q.den}")
    s!"CELL {name} lo=({lo.num} : ℚ) / {lo.den} Fs=({Fs.num} : ℚ) / {Fs.den} Cs=[{lst}] margin={rf (lo - Fs - modP sevWP - mpP)}"
  | none => "none"

#eval emit "A" (1 / 25600) (1 / 12800)
#eval emit "B" (1 / 12800) (1 / 6400)
#eval emit "C" (1 / 6400) (1 / 3200)
#eval emit "D" (1 / 3200) (3 / 6400)
#eval emit "E" (3 / 6400) (1 / 1600)
#eval emit "F" (1 / 800) (1 / 640)
#eval emit "G" (1 / 160) (11 / 1600)
#eval emit "H" (11 / 1600) (3 / 400)
#eval emit "I" (1 / 100) (9 / 800)
#eval emit "J" (1 / 20) (21 / 400)


/-! Line cells (`y = 0`, direction `(1,0)`), `m' = gmin`. -/
def gminP : ℚ := -15724460658777479 / 10000000000000000

def lineCenter (xlo xhi : ℚ) : CQ := ⟨(xlo + xhi) / 2, 0⟩
def lineDir : CQ := ⟨1, 0⟩

def lineData (xlo xhi : ℚ) : Option (List ℚ × ℚ × ℚ × ℚ) :=
  let h := (xhi - xlo) / 2
  let zc := lineCenter xlo xhi
  match aggEval nPilot zc lineDir h sevWP with
  | some (C, F) =>
    let Fs : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
    some (C, loOf (cellPoly C 0 zc lineDir) h, Fs, F)
  | none => none

def lineEmit (name : String) (xlo xhi : ℚ) : String :=
  match lineData xlo xhi with
  | some (C, lo, Fs, F) =>
    let lst := String.intercalate ", " (C.map fun q => s!"(({q.num} : ℤ) : ℚ) / {q.den}")
    s!"LINE {name} lo=({lo.num} : ℚ) / {lo.den} Fs=({Fs.num} : ℚ) / {Fs.den} Cs=[{lst}] margin={rf (lo - Fs - modSum 4 Wp 50 51 sevWP - gminP)}"
  | none => s!"LINE {name} none"


#eval lineEmit "a" (1 / 16) (3 / 32)
#eval lineEmit "b" (3 / 32) (1 / 8)
#eval lineEmit "c" (1 / 1024) (1 / 32)
#eval lineEmit "d" (3 / 5) (7 / 10)

/-- Endpoint cell `[0, 1/1677721600]` of edge 0 (first cell). -/
def epRho : ℚ := (1 / 1677721600 / 2) * (|(-2521 / 5000 : ℚ)| + 1) + Wp
#eval ptOk nPilot sevWP (edge0Center 0 (1 / 1677721600)) epRho 4 cpiP mpP 32 33

end CatalanCore.Uniform.Decay.NearCells.Pilot
