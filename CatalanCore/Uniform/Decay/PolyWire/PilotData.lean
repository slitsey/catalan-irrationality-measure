import CatalanCore.Uniform.Decay.PolyWire.Tables
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Pilot data emitter (lane D, package D11)

The node measure of the D6b pilot (`[0,1]` with density `1`, `[1,7/6]` with density `1/2`,
`RP = CP`) as `nodeSegs`, on the sevenths trial `sevData`.  `#eval` prints Lean definitions of
table cells (untrusted data; the kernel re-runs `aggEval`).
-/

namespace CatalanCore.Uniform.Decay.PolyWire.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearCells.Pilot
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Tools

def pieces0 : List (ℚ × ℚ × ℚ) := [(1, 0, 1), (1 / 2, 1, 7 / 6)]

def nuP : List Seg := nodeSegs pieces0 pieces0

def psP : List WP := cellPieces sevData nuP

def edge0 : Pt × Pt := ((-273 / 2000, 0), (-8809027 / 50000000, 787 / 10000))

def lit (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"

def cpiS : ℚ := cpiOf sevData

/-- Data of a jet cell (`merged = true`: endpoint-merged remainder). -/
def jetData (merged : Bool) (zc dd : CQ) (h : ℚ) : Option (List ℚ × ℚ × ℚ) :=
  match (if merged then NearCells.aggEvalM else NearCells.aggEval) nPilot zc dd h psP with
  | some (C, F) =>
    let Fs : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
    some (C, loOf (cellPoly C cpiS zc dd) h, Fs)
  | none => none

def emitJet (name : String) (merged : Bool) (thr : ℚ) (ulo uhi : ℚ) (zc dd : CQ) (h : ℚ) : String :=
  match jetData merged zc dd h with
  | some (C, lo, Fs) =>
    let lst := String.intercalate ", " (C.map lit)
    s!"DEF {name} lo:={lit lo} Fs:={lit Fs} Cs:=[{lst}] margin:={rf (lo - Fs - modSum 4 Wp 50 51 psP - thr)}"
  | none => s!"DEF {name} none"

def edgeZc (ulo uhi : ℚ) : CQ := edgeCentre (cqOf edge0.1) (cqOf edge0.2) ulo uhi
def edgeDd : CQ := CQ.sub (cqOf edge0.2) (cqOf edge0.1)

def uOf (y : ℚ) : ℚ := y / (787 / 10000)

#eval emitJet "lineL1" false sevData.gmin (1 / 16) (3 / 32) ⟨(1 / 16 + 3 / 32) / 2, 0⟩ ⟨1, 0⟩ ((3 / 32 - 1 / 16) / 2)
#eval emitJet "tubeA" false sevData.mprime (uOf (1 / 25600)) (uOf (1 / 12800))
  (edgeZc (uOf (1 / 25600)) (uOf (1 / 12800))) edgeDd ((uOf (1 / 12800) - uOf (1 / 25600)) / 2)
#eval emitJet "tubeWide" true sevData.mprime (uOf (1 / 204800)) (uOf (1 / 25600))
  (edgeZc (uOf (1 / 204800)) (uOf (1 / 25600))) edgeDd ((uOf (1 / 25600) - uOf (1 / 204800)) / 2)

end CatalanCore.Uniform.Decay.PolyWire.Pilot
