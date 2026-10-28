import CatalanCore.Uniform.Decay.NearCells2.Mix
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch: data generation for the D6d pilots (not part of the library). -/

namespace CatalanCore.Uniform.Decay.NearCells.Pilot
open CatalanCore.Uniform.Decay.Tools

def fl (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30

def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)

def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"

def minE (f : ℕ → Bool) : ℕ := (List.range 200).find? f |>.getD 200

/-- Merged-remainder jet cell on edge 0. -/
def wideData (ylo yhi : ℚ) : String :=
  let h := (yhi - ylo) / 2
  let zc := edge0Center ylo yhi
  match aggEvalM nPilot zc edge0Dir h sevWP with
  | some (C, F) =>
    let Fs := ceil18 F
    let lo := loOf (cellPoly C cpiP zc edge0Dir) h
    s!"WIDE {litQ ylo} {litQ yhi} lo={litQ lo} Fs={litQ Fs} C={litL C} margin={fl (lo - Fs - modSum 4 Wp 50 51 sevWP - mpP)}"
  | none => "WIDE none"

/-- Mixed cell: `sel` marks near pieces. -/
def mixData (n : ℕ) (zc dd : CQ) (h cpi m' : ℚ) (sel : List Bool) : String :=
  let far := (splitSel sevWP sel).1
  let near := (splitSel sevWP sel).2
  let ρ := h * (|dd.re| + |dd.im|) + Wp
  let eW' := minE (fun e => decide (1 ≤ ρ * 2 ^ e))
  let eP' := minE (fun e => decide (1 + 4 / (3 * ρ) ≤ 2 ^ e))
  match aggEvalM n zc dd h far, aggEvalM n zc ⟨1, 0⟩ 0 near with
  | some (C0, F0), some (Cn, Fn) =>
    let C := addL C0 [coeffs Cn 0]
    let Fs := ceil18 (F0 + Fn)
    let lo := loOf (cellPoly C cpi zc dd) h
    s!"MIX rho={litQ ρ} eW'={eW'} eP'={eP'} lo={litQ lo} Fs={litQ Fs} C={litL C} F0={fl F0} Fn={fl Fn} modF={fl (modSum 4 Wp 50 51 far)} modN={fl (modSum 4 ρ eW' eP' near)} margin={fl (lo - Fs - modSum 4 Wp 50 51 far - modSum 4 ρ eW' eP' near - m')}"
  | _, _ => "MIX none"

def selEnd : List Bool := (List.range 29).map fun i => decide (i = 0 ∨ i = 5 ∨ i = 6)
def selLine : List Bool := (List.range 29).map fun i => decide (i = 21 ∨ i = 22 ∨ i = 23)

#eval wideData (1/204800) (1/25600)
#eval wideData (1/6553600) (1/204800)
#eval wideData (1/1677721600) (1/6553600)
#eval mixData 8 (edge0Center 0 (1/1677721600)) edge0Dir (1/1677721600/2) cpiP mpP selEnd
def selL : List Bool := (List.range 29).map fun i => decide (i = 21 ∨ i = 22)
def selR : List Bool := (List.range 29).map fun i => decide (i = 22 ∨ i = 23)
#eval mixData 8 (lineCenter (3/5) (5/8)) lineDir (1/80) 0 gminP selL
#eval mixData 8 (lineCenter (27/40) (7/10)) lineDir (1/80) 0 gminP selR

end CatalanCore.Uniform.Decay.NearCells.Pilot



namespace CatalanCore.Uniform.Decay.NearCells.Pilot
open CatalanCore.Uniform.Decay.Tools
def dbgEnd : List String :=
  let zc := edge0Center 0 (1/1677721600)
  let h : ℚ := 1/1677721600/2
  sevWP.map fun P =>
    s!"{fl P.A.re} far:{(pieceEval2 8 P zc edge0Dir h).isSome} pt:{(pieceEval2 8 P zc ⟨1,0⟩ 0).isSome} z0=({fl (z0of P.A P.B zc).re},{fl (z0of P.A P.B zc).im}) r0={decide (sqrtUp ((q0of (z0of P.A P.B zc) (eof P.A P.B edge0Dir)).nsq * h ^ 2) < 1)} logs={(logHalf (CQ.neg (z0of P.A P.B zc))).isSome},{(argEnc (CQ.neg (z0of P.A P.B zc))).isSome},{(logHalf (CQ.sub CQ.one (z0of P.A P.B zc))).isSome},{(argEnc (CQ.sub CQ.one (z0of P.A P.B zc))).isSome},{(logHalf (CQ.sub P.B P.A)).isSome}"
end CatalanCore.Uniform.Decay.NearCells.Pilot
