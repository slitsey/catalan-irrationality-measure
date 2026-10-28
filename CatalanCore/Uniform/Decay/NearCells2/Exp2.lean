import CatalanCore.Uniform.Decay.NearCells2.Mix
import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch (not part of the library): data for the order-6 cost pilot (D6d, task 3). -/

namespace CatalanCore.Uniform.Decay.NearCells.Pilot
open CatalanCore.Uniform.Decay.Tools

def fl (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30
def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"

def loOfN (n : ℕ) (C : List ℚ) (h : ℚ) : ℚ :=
  let bs := (List.range n).map fun k => bernK (affK (coeffs C) (n - 1) (-h) (2 * h)) (n - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)

def lineDataN (n : ℕ) (xlo xhi : ℚ) : String :=
  let h := (xhi - xlo) / 2
  let zc := lineCenter xlo xhi
  match aggEvalM n zc lineDir h sevWP with
  | some (C, F) =>
    let Fs : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
    let lo := loOfN n (cellPoly C 0 zc lineDir) h
    s!"LINEN lo={litQ lo} Fs={litQ Fs} C={litL C} margin={fl (lo - Fs - modSum 4 Wp 50 51 sevWP - gminP)}"
  | none => "LINEN none"

def rayDataN (n : ℕ) (ylo yhi : ℚ) : String :=
  let h := (yhi - ylo) / 2
  let zc := edge0Center ylo yhi
  match aggEvalM n zc edge0Dir h sevWP with
  | some (C, F) =>
    let Fs : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
    let lo := loOfN n (cellPoly C cpiP zc edge0Dir) h
    s!"RAYN n={n} y=[{fl ylo},{fl yhi}] lo={litQ lo} Fs={litQ Fs} C={litL C} margin={fl (lo - Fs - modSum 4 Wp 50 51 sevWP - mpP)}"
  | none => "RAYN none"

#eval rayDataN 6 (1/25600) (1/12800)
#eval rayDataN 7 (1/25600) (1/12800)
#eval rayDataN 6 (3/6400) (1/1600)
#eval rayDataN 7 (3/6400) (1/1600)
#eval rayDataN 6 (1/800) (1/640)
#eval rayDataN 7 (1/800) (1/640)
#eval rayDataN 6 (1/160) (11/1600)
#eval rayDataN 7 (1/160) (11/1600)
#eval rayDataN 6 (1/100) (9/800)
#eval rayDataN 7 (1/100) (9/800)
#eval rayDataN 6 (1/20) (21/400)
#eval rayDataN 7 (1/20) (21/400)

end CatalanCore.Uniform.Decay.NearCells.Pilot
