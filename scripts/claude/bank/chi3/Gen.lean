import CatalanCore.Uniform.Bank.Common.Data.Chi3.Data
import CatalanCore.Uniform.Bank.Common.Data.Chi3.Frame
import CatalanCore.Uniform.Decay.PolyWire2.Kinds

/-! B3b generator (scratch, not part of the library).  `lean --run Gen.lean spec.txt` reads cell
specs, finds for each the cheapest passing rule (jet orders 5..8, then mix), bisecting on failure,
and prints the cells as integer tapes. -/

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells

namespace B3

def RP : List (ℚ × ℚ × ℚ) := [(1, 0, 1), (1 / 2, 1, 3 / 2)]
def nuC : List Seg := nodeSegs RP RP
def Dc : SplineData := CatalanCore.Uniform.Bank.Common.Data.Chi3.data
def psC : List WP := cellPieces Dc nuC
def Pply : RatPolygon :=
  ⟨49 / 500, (CatalanCore.Uniform.Bank.Common.Data.Chi3.polygon.vertices.tail), 200 / 191⟩
def tmaxC : ℚ := 13943 / 2000
def edgesC : List (Pt × Pt) := edgesAll Pply tmaxC
def Wc : ℚ := Dc.W
def Rtwo : ℚ := 4
def eWc : ℕ := 50
def ePc : ℕ := 51
def Fc : FarData := ⟨5 / 4 * 2 + 5 / 4 * (3 / 2), 4⟩

def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
def floorG (x : ℚ) (g : ℕ) : ℚ := ((x * g).floor : ℤ) / (g : ℚ)
def loOfN (n : ℕ) (C : List ℚ) (h : ℚ) : ℚ :=
  let bs := (List.range n).map fun k => bernK (affK (coeffs C) (n - 1) (-h) (2 * h)) (n - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)
def minE (f : ℕ → Bool) : ℕ := (List.range 200).find? f |>.getD 200

def qf (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den
def oddGrid : ℚ := 3 ^ 40
def rbq (q : ℚ) : ℚ := ((q * oddGrid).floor : ℤ) / oddGrid

def pairInts (q : ℚ) : List Int := [q.num, (q.den : Int)]

/-- A found cell: its kind and its margin `lo - Fs - modSum` (so `m'` can be raised to it). -/
structure Found where
  kind : CellKind2
  margin : ℚ

def evalJet (n : ℕ) (ps : List WP) (zc dd : CQ) (h cpi : ℚ) : Option Found :=
  match aggEvalMF n zc dd h ps with
  | some (C, F) =>
    let Fs := ceil18 F
    let lo := loOfN n (cellPoly C cpi zc dd) h
    some ⟨.jetF n lo C Fs, lo - Fs - modSum Rtwo Wc eWc ePc ps⟩
  | none => none

def evalMix (n : ℕ) (ps : List WP) (sel : List Bool) (zc dd : CQ) (h cpi : ℚ) : Option Found :=
  let far := (splitSel ps sel).1
  let near := (splitSel ps sel).2
  let ρ := h * (|dd.re| + |dd.im|) + Wc
  let eW' := minE (fun e => decide (1 ≤ ρ * 2 ^ e))
  let eP' := minE (fun e => decide (1 + Rtwo / (3 * ρ) ≤ 2 ^ e))
  match aggEvalMF n zc dd h far, aggEvalMF n zc ⟨1, 0⟩ 0 near with
  | some (C0, F0), some (Cn, Fn) =>
    let C := addL C0 [coeffs Cn 0]
    let Fs := ceil18 (F0 + Fn)
    let lo := loOfN n (cellPoly C cpi zc dd) h
    some ⟨.mixF n sel ρ lo C Fs eW' eP',
      lo - Fs - modSum Rtwo Wc eWc ePc far - modSum Rtwo ρ eW' eP' near⟩
  | _, _ => none

def checkKind (ps : List WP) (zc dd : CQ) (h cpi m' : ℚ) (k : CellKind2) : Bool :=
  kindOk2 ps zc dd h Wc Rtwo cpi m' eWc ePc k

/-- distance from `z` to the segment `[A, B]` (floats) -/
def segDist (z : CQ) (P : WP) : Float :=
  let ax := qf P.A.re; let ay := qf P.A.im; let bx := qf P.B.re; let by_ := qf P.B.im
  let zx := qf z.re; let zy := qf z.im
  let dx := bx - ax; let dy := by_ - ay
  let l2 := dx * dx + dy * dy
  let t0 := ((zx - ax) * dx + (zy - ay) * dy) / l2
  let t := if t0 < 0 then 0 else if t0 > 1 then 1 else t0
  let px := ax + t * dx; let py := ay + t * dy
  Float.sqrt ((zx - px) * (zx - px) + (zy - py) * (zy - py))

def selFor (ps : List WP) (zc dd : CQ) (h : ℚ) (K : Float) : List Bool :=
  let R := qf (h * (|dd.re| + |dd.im|) + Wc)
  ps.map fun P => decide (segDist zc P ≤ K * R) || (aggEvalMF 8 zc dd h [P]).isNone

/-- Try all rules for the cell; `m'` is the target threshold. -/
def solveOne (ps : List WP) (zc dd : CQ) (h cpi m' : ℚ) : Option Found := Id.run do
  for n in [5, 6, 7, 8] do
    match evalJet n ps zc dd h cpi with
    | some f => if checkKind ps zc dd h cpi m' f.kind then return some f
    | none => pure ()
  for K in [8.0, 3.0, 30.0, 100.0] do
    let sel := selFor ps zc dd h K
    if sel.any id then
      for n in [8, 6] do
        match evalMix n ps sel zc dd h cpi with
        | some f => if checkKind ps zc dd h cpi m' f.kind then return some f
        | none => pure ()
  return none

def kindInts : CellKind2 → List Int
  | .far => [(0 : Int)]
  | .jetF n lo C Fs => [(1 : Int), n, lo.num, (lo.den : Int), Fs.num, (Fs.den : Int), C.length] ++
      (C.map pairInts).flatten
  | .mixF n sel ρ lo C Fs eW' eP' => [(2 : Int), n, ρ.num, (ρ.den : Int), lo.num, (lo.den : Int), Fs.num,
      (Fs.den : Int), eW', eP', sel.length] ++ (sel.map fun b => if b then (1 : Int) else 0) ++
      [(C.length : Int)] ++ (C.map pairInts).flatten

def showInts (l : List Int) : String := " ".intercalate (l.map toString)

/-- split point for a failing cell `[a, b]` in `[0, 1]`-like parameter (u) -/
def splitPoint (a b : ℚ) (lo hi : ℚ) : ℚ :=
  let mid := (a + b) / 2
  let da := a - lo; let db := hi - b
  if a == lo && b - a > 0 then rbq (a + (b - a) / 32)
  else if b == hi && b - a > 0 then rbq (b - (b - a) / 32)
  else if da > 0 && b - lo > 4 * da then
    let g := Float.sqrt (qf da * qf (b - lo)); rbq (lo + ((g * 1e18).floor.toUInt64.toNat : ℚ) / 1e18)
  else if db > 0 && hi - a > 4 * db then
    let g := Float.sqrt (qf db * qf (hi - a)); rbq (hi - ((g * 1e18).floor.toUInt64.toNat : ℚ) / 1e18)
  else rbq mid

/-- Solve a cell, bisecting on failure.  `geom a b` gives centre/direction/half-width. -/
partial def solveCell (ps : List WP) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' lo hi : ℚ)
    (a b : ℚ) (farOk : ℚ → ℚ → Bool) (depth : ℕ) : List (ℚ × ℚ × Option Found) :=
  if farOk a b then [(a, b, some ⟨.far, 0⟩)] else
  let (zc, dd, h) := geom a b
  match solveOne ps zc dd h cpi m' with
  | some f => [(a, b, some f)]
  | none =>
    if depth > 40 then [(a, b, none)] else
    let s := splitPoint a b lo hi
    let s := if s ≤ a || s ≥ b then (a + b) / 2 else s
    solveCell ps geom cpi m' lo hi a s farOk (depth + 1) ++
      solveCell ps geom cpi m' lo hi s b farOk (depth + 1)

def tubeGeom (e : Pt × Pt) (a b : ℚ) : CQ × CQ × ℚ :=
  (edgeCentre (cqOf e.1) (cqOf e.2) a b, CQ.sub (cqOf e.2) (cqOf e.1), (b - a) / 2)

def lineGeom (a b : ℚ) : CQ × CQ × ℚ := (⟨(a + b) / 2, 0⟩, ⟨1, 0⟩, (b - a) / 2)

def cpiC : ℚ := cpiOf Dc

def negW (P : WP) : WP := { P with w := -P.w }

def qOf (n d : String) : ℚ := (n.toInt! : ℚ) / (d.toNat! : ℚ)


def capEnds : List ℚ := psC.filterMap fun P => if P.A.im == 0 && P.B.im == 0 then some P.A.re else none

def bestCap (ps' : List WP) (a b : ℚ) : Option (ℚ × Found) := Id.run do
  let (zc, dd, h) := lineGeom a b
  let mut res : Option Found := none
  match evalJet 8 ps' zc dd h 0 with
  | some f => res := some f
  | none =>
    for K in [8.0, 3.0, 30.0] do
      if res.isNone then
        let sel := selFor ps' zc dd h K
        if sel.any id then
          match evalMix 8 ps' sel zc dd h 0 with
          | some f => res := some f
          | none => pure ()
  match res with
  | some f =>
    let m'' := floorG f.margin (10 ^ 15)
    if checkKind ps' zc dd h 0 m'' f.kind then return some (-m'', f) else return none
  | none => return none

partial def solveCap (ps' : List WP) (a b : ℚ) (depth : ℕ) : List (ℚ × ℚ × Option (ℚ × Found)) :=
  let r := bestCap ps' a b
  let good := match r with
    | some (ub, _) => (b - a) * max (ub - Dc.mprime) 0 ≤ 1 / 2000000000 || b - a < 1 / 10 ^ 13
    | none => false
  if good then [(a, b, r)] else
  if depth > 60 then [(a, b, r)] else
  let ends := capEnds
  let s := if ends.contains a then rbq (a + (b - a) / 16)
    else if ends.contains b then rbq (b - (b - a) / 16) else rbq ((a + b) / 2)
  let s := if s ≤ a || s ≥ b then (a + b) / 2 else s
  solveCap ps' a s (depth + 1) ++ solveCap ps' s b (depth + 1)

def process (line : String) : IO Unit := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  match ws with
  | ["T", ei, an, ad, bn, bd] =>
    let e := edgesC.getD ei.toNat! ((0, 0), (0, 0))
    let a := qOf an ad; let b := qOf bn bd
    let res := solveCell psC (tubeGeom e) cpiC Dc.mprime 0 1 a b
      (fun a b => cellFarOk Dc Fc e (a, b)) 0
    for (x, y, f) in res do
      match f with
      | some f => IO.println s!"T {ei} {x.num} {x.den} {y.num} {y.den} | {showInts (kindInts f.kind)}"
      | none => IO.println s!"FAIL T {ei} {x.num} {x.den} {y.num} {y.den}"
  | ["L", an, ad, bn, bd] =>
    let a := qOf an ad; let b := qOf bn bd
    let res := solveCell psC lineGeom cpiC Dc.gmin 0 1 a b (fun _ _ => false) 0
    for (x, y, f) in res do
      match f with
      | some f => IO.println s!"L {x.num} {x.den} {y.num} {y.den} | {showInts (kindInts f.kind)}"
      | none => IO.println s!"FAIL L {x.num} {x.den} {y.num} {y.den}"
  | ["C", an, ad, bn, bd] =>
    let a := qOf an ad; let b := qOf bn bd
    for (x, y, r) in solveCap (psC.map negW) a b 0 do
      match r with
      | some (ub, f) =>
        IO.println s!"C {x.num} {x.den} {y.num} {y.den} | {ub.num} {ub.den} | {showInts (kindInts f.kind)}"
      | none => IO.println s!"FAIL C {x.num} {x.den} {y.num} {y.den}"
  | ["D", ei, an, ad, bn, bd] =>
    let e := edgesC.getD ei.toNat! ((0, 0), (0, 0))
    let a := qOf an ad; let b := qOf bn bd
    let (zc, dd, h) := tubeGeom e a b
    IO.println s!"zc {qf zc.re} {qf zc.im} dd {qf dd.re} {qf dd.im} h {qf h} target {qf Dc.mprime}"
    for n in [5, 8] do
      match evalJet n psC zc dd h cpiC with
      | some f => IO.println s!"jet {n} margin-m' {qf (f.margin - Dc.mprime)}"
      | none => IO.println s!"jet {n} none"
    for K in [3.0, 8.0, 30.0] do
      let sel := selFor psC zc dd h K
      IO.println s!"K {K} near {sel.filter id |>.length} idx {(List.range sel.length).filter (fun i => sel.getD i false)}"
      let far := (splitSel psC sel).1
      let near := (splitSel psC sel).2
      IO.println s!"far {(aggEvalMF 8 zc dd h far).isSome} near {(aggEvalMF 8 zc ⟨1, 0⟩ 0 near).isSome} nearEach {near.map fun P => (aggEvalMF 8 zc ⟨1, 0⟩ 0 [P]).isSome} farEach {(far.map fun P => (aggEvalMF 8 zc dd h [P]).isSome).filter not |>.length}"
      match evalMix 8 psC sel zc dd h cpiC with
      | some f => IO.println s!"mix margin-m' {qf (f.margin - Dc.mprime)}"
      | none => IO.println s!"mix none"
  | _ => IO.eprintln s!"bad line {line}"

end B3

def main (args : List String) : IO Unit := do
  match args with
  | [file, k, nslices] =>
    let lines ← IO.FS.lines file
    let mut i := 0
    for l in lines do
      if i % nslices.toNat! == k.toNat! then
        B3.process l
        (← IO.getStdout).flush
      i := i + 1
  | _ => IO.eprintln "usage: Gen spec k nslices"
