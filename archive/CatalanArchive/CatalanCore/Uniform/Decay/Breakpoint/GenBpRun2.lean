import CatalanCore.Uniform.Decay.Breakpoint.GenBp
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanCore.Uniform.Decay.Breakpoint.GenBp
open CatalanCore.Uniform.Bank.Chi3

def lmaxOf (ei : ℕ) (up : ℚ) (side : Bool) : ℚ :=
  let bs := bps edgesLit[ei]!
  if side then
    up - ((bs.filter (· < up)).foldl max 0)
  else
    ((bs.filter (· > up)).foldl min 1) - up

def sortQ (l : List ℚ) : List ℚ := l.mergeSort (fun a b => decide (a ≤ b))

def sites : List (String × ℕ × ℚ × Bool) :=
  (List.range 6).flatMap fun ei =>
    let bs := sortQ (bps edgesLit[ei]!)
    (bs.zipIdx).flatMap fun (u, j) =>
      (if u < 1 then [(s!"bp_e{ei}_{j}r", ei, u, false)] else []) ++
      (if 0 < u then [(s!"bp_e{ei}_{j}l", ei, u, true)] else [])

def run (nm : String) (ei : ℕ) (up : ℚ) (side : Bool) : String :=
  let L := findL ei up side 8 (lmaxOf ei up side)
  s!"{nm} L={fl L}\n" ++ report ei up side 8 L ++ "\n" ++ thm nm ei up side 8 L

#eval sites.map fun (nm, ei, up, side) => run nm ei up side

end CatalanCore.Uniform.Decay.Breakpoint.GenBp
