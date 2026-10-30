import CatalanCore.Uniform.Bank.Chi3.Env
import CatalanCore.Uniform.Decay.FarField.PLKinds
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch (not part of the library): data generation for the PL cap pilot (lane D, D15).
`genPL name x0 x1` prints the Lean source of the PL cap cell on `[x0, x1]` whose majorant is the
tangent of the jet at the centre, shifted up by `Fs + modSum - lo` and rounded up to the `1e-18` grid. -/

namespace CatalanCore.Uniform.Decay.FarField.Gen
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearCells.Pilot
  CatalanCore.Uniform.Decay.NearFast CatalanCore.Uniform.Decay.PolyWire2 CatalanCore.Uniform.Bank.Chi3
  CatalanCore.Uniform.Decay.Tools

def negPs : List WP := (cellPieces Dn nuC).map negW

def fl18 (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30
def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"

def genPL (name : String) (x0 x1 : ℚ) : IO Unit := do
  let xc := (x0 + x1) / 2
  let h := (x1 - x0) / 2
  match aggEvalMF 8 ⟨xc, 0⟩ ⟨1, 0⟩ h negPs with
  | none => IO.println s!"-- {name}: aggEvalMF none"
  | some (C, F) =>
    let Fs := ceil18 F
    let md := modSum Rtw Dn.W eWc ePc negPs
    let α0 := -(coeffs C 0)
    let β0 := -(coeffs C 1)
    let lo0 := loOf (addL (cellPoly C 0 ⟨xc, 0⟩ ⟨1, 0⟩) [α0, β0]) h
    let extra := (max 0 (Fs + md - lo0)) + 1 / 10 ^ 16
    let ua := ceil18 (α0 + extra - β0 * h)
    let ub := ceil18 (α0 + extra + β0 * h)
    let α := (ua + ub) / 2
    let β := (ub - ua) / (2 * h)
    let lo := loOf (addL (cellPoly C 0 ⟨xc, 0⟩ ⟨1, 0⟩) [α, β]) h
    let over := (x1 - x0) * (max (ua - Dn.mprime) 0 + max (ub - Dn.mprime) 0) / 2
    IO.println s!"-- {name}: width {fl18 (x1 - x0)} Fs {fl18 Fs} mod {fl18 md} margin {fl18 (lo - Fs - md)} ua-m' {fl18 (ua - Dn.mprime)} ub-m' {fl18 (ub - Dn.mprime)} overshoot {fl18 over}"
    IO.println s!"def {name} : PLCap := ⟨({litQ x0}, {litQ x1}, {litQ ua}, {litQ ub}), .lin 8 ({litQ lo}) {litL C} ({litQ Fs})⟩"

-- window B: k03_02 .. k04_11 = [-0.09503125, -0.094375]
#eval genPL "pcB1" (-9503125 / 100000000) (-9490000 / 100000000)
#eval genPL "pcB1w" (-9503125 / 100000000) (-9480000 / 100000000)
#eval genPL "pcB1x" (-9503125 / 100000000) (-9470000 / 100000000)
#eval genPL "pcB2" (-9490000 / 100000000) (-9470000 / 100000000)
#eval genPL "pcB3" (-9470000 / 100000000) (-9450000 / 100000000)
#eval genPL "pcB4" (-9450000 / 100000000) (-9437500 / 100000000)

end CatalanCore.Uniform.Decay.FarField.Gen
