import CatalanCore.Uniform.Decay.NearFast.Cell
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch: data generation for the D12 pilots (not part of the library). -/

namespace CatalanCore.Uniform.Decay.NearFast.Gen
open CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearCells.Pilot CatalanCore.Uniform.Decay.Tools

def fl' (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30
def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"
def minE (f : ℕ → Bool) : ℕ := (List.range 200).find? f |>.getD 200

def jetCell (name zcS hS : String) (zc dd : CQ) (h cpi m' : ℚ) : String :=
  match aggEvalMF nPilot zc dd h sevWP with
  | some (C, F) =>
    let Fs := ceil18 F
    let lo := loOf (cellPoly C cpi zc dd) h
    let cpiS := if cpi = 0 then "0" else "cpiP"
    let mS := if m' = mpP then "mpP" else "gminP"
    let ddS := if dd.im = 0 then "lineDir" else "edge0Dir"
    s!"theorem {name} : cellOkF nPilot sevWP {zcS} {ddS} {hS} Wp 4 {cpiS} ({litQ lo}) {mS} {litL C} ({litQ Fs}) 50 51 = true := by decide +kernel -- margin {fl' (lo - Fs - modSum 4 Wp 50 51 sevWP - m')}"
  | none => s!"-- {name} none"

/-- Round to the odd grid `3^-40` (data-level 2-adic de-structuring). -/
def rb (q : ℚ) : ℚ := (⌊q * 3 ^ 40⌋ : ℤ) / (3 ^ 40 : ℚ)
def litB (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"

def edgeCell (name : String) (y0 y1 : ℚ) : String :=
  let ylo := rb y0
  let yhi := rb y1
  jetCell name s!"(edge0Center ({litB ylo}) ({litB yhi}))" s!"((({litB yhi}) - ({litB ylo})) / 2)" (edge0Center ylo yhi) edge0Dir ((yhi - ylo) / 2) cpiP mpP

def lineCell (name : String) (x0 x1 : ℚ) : String :=
  let xlo := rb x0
  let xhi := rb x1
  jetCell name s!"(lineCenter ({litB xlo}) ({litB xhi}))" s!"((({litB xhi}) - ({litB xlo})) / 2)" (lineCenter xlo xhi) lineDir ((xhi - xlo) / 2) 0 gminP

def mixCell (name : String) (zcS ddS hS : String) (n : ℕ) (zc dd : CQ) (h cpi m' : ℚ) (selS : String) (sel : List Bool) : String :=
  let far := (splitSel sevWP sel).1
  let near := (splitSel sevWP sel).2
  let ρ := h * (|dd.re| + |dd.im|) + Wp
  let eW' := minE (fun e => decide (1 ≤ ρ * 2 ^ e))
  let eP' := minE (fun e => decide (1 + 4 / (3 * ρ) ≤ 2 ^ e))
  match aggEvalMF n zc dd h far, aggEvalMF n zc ⟨1, 0⟩ 0 near with
  | some (C0, F0), some (Cn, Fn) =>
    let C := addL C0 [coeffs Cn 0]
    let Fs := ceil18 (F0 + Fn)
    let lo := loOf (cellPoly C cpi zc dd) h
    let cpiS := if cpi = 0 then "0" else "cpiP"
    let mS := if m' = mpP then "mpP" else "gminP"
    s!"theorem {name} : mixOkF {n} (splitSel sevWP {selS}).1 (splitSel sevWP {selS}).2 {zcS} {ddS} {hS} ({litQ ρ}) Wp 4 {cpiS} ({litQ lo}) {mS} {litL C} ({litQ Fs}) 50 51 {eW'} {eP'} = true := by decide +kernel -- margin {fl' (lo - Fs - modSum 4 Wp 50 51 far - modSum 4 ρ eW' eP' near - m')}"
  | _, _ => s!"-- {name} none"

def mixEdge (name : String) (y0 y1 : ℚ) (sel : List Bool) (selS : String) : String :=
  let ylo := rb y0
  let yhi := rb y1
  let h := (yhi - ylo) / 2
  mixCell name s!"(edge0Center ({litB ylo}) ({litB yhi}))" "edge0Dir" s!"((({litB yhi}) - ({litB ylo})) / 2)" 8 (edge0Center ylo yhi) edge0Dir h cpiP mpP selS sel

def mixLine (name : String) (x0 x1 : ℚ) (sel : List Bool) (selS : String) : String :=
  let xlo := rb x0
  let xhi := rb x1
  let h := (xhi - xlo) / 2
  mixCell name s!"(lineCenter ({litB xlo}) ({litB xhi}))" "lineDir" s!"((({litB xhi}) - ({litB xlo})) / 2)" 8 (lineCenter xlo xhi) lineDir h 0 gminP selS sel

def selEnd : List Bool := (List.range 29).map fun i => decide (i = 0 ∨ i = 5 ∨ i = 6)
def selL : List Bool := (List.range 29).map fun i => decide (i = 21 ∨ i = 22)
def selR : List Bool := (List.range 29).map fun i => decide (i = 22 ∨ i = 23)

#eval IO.println (edgeCell "cellA" (1/25600) (1/12800))
#eval IO.println (edgeCell "cellB" (1/12800) (1/6400))
#eval IO.println (edgeCell "cellC" (1/6400) (1/3200))
#eval IO.println (edgeCell "cellD" (1/3200) (3/6400))
#eval IO.println (edgeCell "cellE" (3/6400) (1/1600))
#eval IO.println (edgeCell "cellF" (1/800) (1/640))
#eval IO.println (edgeCell "cellG" (1/160) (11/1600))
#eval IO.println (edgeCell "cellH" (11/1600) (3/400))
#eval IO.println (edgeCell "cellI" (1/100) (9/800))
#eval IO.println (edgeCell "cellJ" (1/20) (21/400))
#eval IO.println (edgeCell "wideA" (1/204800) (1/25600))
#eval IO.println (edgeCell "wideB" (1/6553600) (1/204800))
#eval IO.println (edgeCell "wideC" (1/1677721600) (1/6553600))
#eval IO.println (lineCell "linea" (1/16) (3/32))
#eval IO.println (lineCell "lineb" (3/32) (1/8))
#eval IO.println (lineCell "linec" (1/1024) (1/32))
#eval IO.println (mixEdge "mixEnd" 0 (1/1677721600) selEnd "selEnd")
#eval IO.println (mixLine "mixLineL" (3/5) (5/8) selL "selL")
#eval IO.println (mixLine "mixLineR" (27/40) (7/10) selR "selR")

end CatalanCore.Uniform.Decay.NearFast.Gen
