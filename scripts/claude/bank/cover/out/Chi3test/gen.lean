import CatalanCore.Uniform.Bank.Chi3.Cover.Env0
import CatalanCore.Uniform.Decay.PolyWire3.Decode

/-! Bank-generic cell generator (lane D, D17; scratch, not part of the library).  The Python driver
`cover.py` substitutes `CatalanCore.Uniform.Bank.Chi3.Cover.Env0` / `CatalanCore.Uniform.Bank.Chi3.Cover` (the bank's `Env0` module and namespace) and runs
`lean --run GenCover.lean <spec> <k> <nslices>`.  One output line per cell, kind tapes as in
`PolyWire3.Decode`.  Every printed cell has passed the library Boolean `kindOk` (so nothing is
trusted from the search).  Cell kinds tried: far (bank rule), multipole `mp`, jets of order 5..8,
mixed (near pieces by distance), and the breakpoint cell `bp` next to every piece endpoint.  Spec
lines: `T e` (tube edge e), `L` (line), `C` (cap), `M cre_n cre_d cim_n cim_d K J`. -/

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearFast
  CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Breakpoint CatalanCore.Uniform.Decay.FarField
  CatalanCore.Uniform.Bank.Chi3.Cover

namespace GenC

def Dc : SplineData := Dn0
def psC : List WP := cellPieces Dc nuC
def edgesC : List (Pt × Pt) := edgesAll Pply tmaxC
def Wc : ℚ := Dc.W

def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
def floorG (x : ℚ) (g : ℕ) : ℚ := ((x * g).floor : ℤ) / (g : ℚ)
def minE (f : ℕ → Bool) : ℕ := (List.range 200).find? f |>.getD 200
def qf (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den
def oddGrid : ℚ := 3 ^ 40
def rbq (q : ℚ) : ℚ := ((q * oddGrid).floor : ℤ) / oddGrid
def pairInts (q : ℚ) : List Int := [q.num, (q.den : Int)]
def qOf (n d : String) : ℚ := (n.toInt! : ℚ) / (d.toNat! : ℚ)

/-- lower / upper rational square roots on the grid `1/10^4` -/
def sqrtLo (q : ℚ) : ℚ := ((Nat.sqrt ((q * 10 ^ 8).floor.toNat) : ℕ) : ℚ) / 10 ^ 4
def sqrtHi (q : ℚ) : ℚ := (((Nat.sqrt ((q * 10 ^ 8).ceil.toNat) : ℕ) : ℚ) + 1) / 10 ^ 4

structure Found where
  kind : CatalanCore.Uniform.Decay.PolyWire3.CellKind
  margin : ℚ

def loOfNh (n : ℕ) (C : List ℚ) (h : ℚ) : ℚ :=
  let bs := (List.range n).map fun k => bernK (affK (coeffs C) (n - 1) (-h) (2 * h)) (n - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)

def loOfN0 (n : ℕ) (C : List ℚ) (S : ℚ) : ℚ :=
  let bs := (List.range n).map fun k => bernK (affK (coeffs C) (n - 1) 0 S) (n - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)

def evalJet (n : ℕ) (ps : List WP) (zc dd : CQ) (h cpi : ℚ) : Option Found :=
  match aggEvalMF n zc dd h ps with
  | some (C, F) =>
    let Fs := ceil18 F
    let lo := loOfNh n (cellPoly C cpi zc dd) h
    some ⟨.base (.jetF n lo C Fs), lo - Fs - modSum Rtw Wc eWc ePc ps⟩
  | none => none

def evalMix (n : ℕ) (ps : List WP) (sel : List Bool) (zc dd : CQ) (h cpi : ℚ) : Option Found :=
  let far := (splitSel ps sel).1
  let near := (splitSel ps sel).2
  let ρ := h * (|dd.re| + |dd.im|) + Wc
  let eW' := minE (fun e => decide (1 ≤ ρ * 2 ^ e))
  let eP' := minE (fun e => decide (1 + Rtw / (3 * ρ) ≤ 2 ^ e))
  match aggEvalMF n zc dd h far, aggEvalMF n zc ⟨1, 0⟩ 0 near with
  | some (C0, F0), some (Cn, Fn) =>
    let C := addL C0 [coeffs Cn 0]
    let Fs := ceil18 (F0 + Fn)
    let lo := loOfNh n (cellPoly C cpi zc dd) h
    some ⟨.base (.mixF n sel ρ lo C Fs eW' eP'),
      lo - Fs - modSum Rtw Wc eWc ePc far - modSum Rtw ρ eW' eP' near⟩
  | _, _ => none

def evalBp (n : ℕ) (side : Bool) (ps : List WP) (zc dd : CQ) (h cpi : ℚ) : Option Found :=
  let p := bpPoint side zc dd h
  let d' := bpDir side dd
  let S := 2 * h
  match aggEvalMF n p d' S (bpFar p ps), incAgg n d' S (bpInc p ps) with
  | some (Cf, Ff), some (Ci, Bi, Fi) =>
    let C := addL Cf Ci
    let eS := minE (fun k => decide (1 ≤ S * 2 ^ k))
    let logb := lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10))
    let Fs := ceil18 (Ff + Fi + logb)
    let lo := loOfN0 n (cellPoly C cpi p d') S
    some ⟨.bp n side lo C Fs eS, lo - Fs - modSum Rtw Wc eWc ePc ps⟩
  | _, _ => none

def checkKind (ps : List WP) (M : Option MPData) (zc dd : CQ) (h cpi m' : ℚ) (k : CatalanCore.Uniform.Decay.PolyWire3.CellKind) : Bool :=
  kindOk ps M zc dd h Wc Rtw cpi m' eWc ePc k

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

/-- the multipole cell, if the cell lies outside the disc -/
def mpTry (ps : List WP) (M : Option MPData) (zc dd : CQ) (h cpi m' : ℚ) : Option Found :=
  match M with
  | none => none
  | some M0 =>
    let u0 := CQ.sub zc M0.c
    let rm := sqrtLo u0.nsq
    let rh := sqrtHi (dd.nsq * h ^ 2)
    let k : CatalanCore.Uniform.Decay.PolyWire3.CellKind := .mp rm rh
    if rm - (rh + Wc) > M0.R && checkKind ps M zc dd h cpi m' k then some ⟨k, 0⟩ else none

/-- Jets, multipole, mixed rules for one cell (not breakpoint cells). -/
def solveOne (ps : List WP) (M : Option MPData) (zc dd : CQ) (h cpi m' : ℚ) : Option Found := Id.run do
  match mpTry ps M zc dd h cpi m' with
  | some f => return some f
  | none => pure ()
  for n in [5, 6, 7, 8] do
    match evalJet n ps zc dd h cpi with
    | some f => if checkKind ps M zc dd h cpi m' f.kind then return some f
    | none => pure ()
  for K in [8.0, 3.0, 30.0, 100.0] do
    let sel := selFor ps zc dd h K
    if sel.any id then
      for n in [8, 6] do
        match evalMix n ps sel zc dd h cpi with
        | some f => if checkKind ps M zc dd h cpi m' f.kind then return some f
        | none => pure ()
  return none

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

partial def solveCell (ps : List WP) (M : Option MPData) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' lo hi : ℚ)
    (a b : ℚ) (farOk : ℚ → ℚ → Bool) (depth : ℕ) : List (ℚ × ℚ × Option Found) :=
  if farOk a b then [(a, b, some ⟨.base .far, 0⟩)] else
  let (zc, dd, h) := geom a b
  match solveOne ps M zc dd h cpi m' with
  | some f => [(a, b, some f)]
  | none =>
    if depth > 40 then [(a, b, none)] else
    let s := splitPoint a b lo hi
    let s := if s ≤ a || s ≥ b then (a + b) / 2 else s
    solveCell ps M geom cpi m' lo hi a s farOk (depth + 1) ++
      solveCell ps M geom cpi m' lo hi s b farOk (depth + 1)

/-- One trial cell `[a, e]`: the bank's far rule, else jets / multipole / mixed. -/
def trialCell (ps : List WP) (M : Option MPData) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' : ℚ)
    (farOk : ℚ → ℚ → Bool) (a e : ℚ) : Option Found :=
  if farOk a e then some ⟨.base .far, 0⟩ else
  let (zc, dd, h) := geom a e
  solveOne ps M zc dd h cpi m'

def stepTo (b a w : ℚ) : ℚ :=
  if a + w ≥ b then b else
  let e := rbq (a + w)
  if e ≤ a then b else e

/-- Greedy cover of `[a, b]` (D17 fix, 28 Oct): from the left, the widest admissible cell by gallop
(factor 3/2) from the previous width, then three bisection steps; every cell is still verified by `kindOk`. -/
partial def greedyCover (ps : List WP) (M : Option MPData) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' : ℚ)
    (farOk : ℚ → ℚ → Bool) (a b : ℚ) (w : ℚ) (fuel : ℕ) : List (ℚ × ℚ × Option Found) :=
  if a ≥ b then [] else
  if fuel = 0 then [(a, b, none)] else
  let tr := trialCell ps M geom cpi m' farOk a
  match (if b - a ≤ 2 * w then tr b else none) with
  | some f => [(a, b, some f)]
  | none =>
    -- find a working width
    let w0 := if w ≤ 0 || a + w ≥ b then (b - a) / 2 else w
    let rec shrink (w : ℚ) (k : ℕ) : Option (ℚ × Found) :=
      match k with
      | 0 => none
      | k + 1 =>
        let e := stepTo b a w
        match tr e with
        | some f => some (e, f)
        | none => shrink (w * 2 / 3) k
    match shrink w0 90 with
    | none => [(a, b, none)]
    | some (e0, f0) =>
      -- gallop upward
      let rec up (e : ℚ) (f : Found) (k : ℕ) : (ℚ × Found) × ℚ :=
        match k with
        | 0 => ((e, f), e)
        | k + 1 =>
          if e ≥ b then ((e, f), e) else
          let e' := stepTo b a ((e - a) * 3 / 2)
          match tr e' with
          | some f' => up e' f' k
          | none => ((e, f), e')
      let ((e1, f1), eb) := up e0 f0 60
      let rec refine (lo : ℚ) (fl : Found) (hi : ℚ) (k : ℕ) : ℚ × Found :=
        match k with
        | 0 => (lo, fl)
        | k + 1 =>
          if eb == e1 then (lo, fl) else
          let mid := rbq ((lo + hi) / 2)
          if mid ≤ lo || mid ≥ hi then (lo, fl) else
          match tr mid with
          | some f => refine mid f hi k
          | none => refine lo fl mid k
      let (e2, f2) := if e1 ≥ b then (e1, f1) else refine e1 f1 eb 3
      (a, e2, some f2) :: greedyCover ps M geom cpi m' farOk e2 b (e2 - a) (fuel - 1)

def tubeGeom (e : Pt × Pt) (a b : ℚ) : CQ × CQ × ℚ :=
  (edgeCentre (cqOf e.1) (cqOf e.2) a b, CQ.sub (cqOf e.2) (cqOf e.1), (b - a) / 2)

def lineGeom (a b : ℚ) : CQ × CQ × ℚ := (⟨(a + b) / 2, 0⟩, ⟨1, 0⟩, (b - a) / 2)

def cpiC : ℚ := cpiOf Dc

/-! ### breakpoints -/

def onEdge (e : Pt × Pt) (x : CQ) : Option ℚ :=
  let a := cqOf e.1
  let b := cqOf e.2
  let d := CQ.sub b a
  let u := if d.re ≠ 0 then (x.re - a.re) / d.re else (x.im - a.im) / d.im
  if x.re = a.re + u * d.re ∧ x.im = a.im + u * d.im ∧ 0 ≤ u ∧ u ≤ 1 then some u else none

def sortQ (l : List ℚ) : List ℚ := (l.toArray.qsort (· < ·)).toList

def edgeBps (e : Pt × Pt) : List ℚ :=
  sortQ ((psC.flatMap fun P => [onEdge e P.A, onEdge e P.B]).filterMap id).eraseDups

/-- breakpoints on the real axis within `[lo, hi]` -/
def realBps (lo hi : ℚ) : List ℚ :=
  sortQ ((psC.flatMap fun P => [P.A, P.B]).filter (fun z => z.im == 0 && lo ≤ z.re && z.re ≤ hi)
    |>.map (·.re)).eraseDups

/-- Largest breakpoint cell next to the breakpoint `x` (`side = false`: cell `[x, x+L]`; `true`:
`[x-L, x]`), `L ≤ Lmax`, by a halving ladder and bisection. -/
def bpCellAt (ps : List WP) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' : ℚ) (x Lmax : ℚ) (side : Bool) :
    Option (ℚ × ℚ × Found) := Id.run do
  let okL := fun (L : ℚ) => Id.run do
    let (a, b) := if side then (x - L, x) else (x, x + L)
    let (zc, dd, h) := geom a b
    let mut res : Option Found := none
    for n in [8, 6, 5] do
      if res.isNone then
        match evalBp n side ps zc dd h cpi with
        | some f => if checkKind ps none zc dd h cpi m' f.kind then res := some f
        | none => pure ()
    match res with
    | some f => return some (a, b, f)
    | none => return none
  let mut found : Option (ℚ × ℚ × Found) := none
  let mut Lok : ℚ := 0
  let mut Lbad : ℚ := 0
  for k in List.range 70 do
    if found.isNone then
      let L := rbq (Lmax / 2 ^ k)
      if L > 0 then
        match okL L with
        | some r => found := some r; Lok := L; Lbad := if k = 0 then L else rbq (Lmax / 2 ^ (k - 1))
        | none => pure ()
  if found.isNone then return none
  if Lbad == Lok then return found
  for _ in List.range 9 do
    let mid := rbq ((Lok + Lbad) / 2)
    if mid > Lok && mid < Lbad then
      match okL mid with
      | some r => found := some r; Lok := mid
      | none => Lbad := mid
  return found

/-- Cover `[x, y]` (adjacent breakpoints `xb`, `yb` flags) : breakpoint cells at the flagged ends,
then jets / multipole / mixed in between. -/
def coverSeg (ps : List WP) (M : Option MPData) (geom : ℚ → ℚ → CQ × CQ × ℚ) (cpi m' : ℚ)
    (x y : ℚ) (xb yb : Bool) (farOk : ℚ → ℚ → Bool) : List (ℚ × ℚ × Option Found) := Id.run do
  let mut out : List (ℚ × ℚ × Option Found) := []
  let mut lo := x
  let mut hi := y
  let Lmax := min (y - x) (1 / 3)
  if xb then
    match bpCellAt ps geom cpi m' x (if yb then Lmax / 2 else Lmax) false with
    | some (a, b, f) => out := out ++ [(a, b, some f)]; lo := b
    | none => pure ()
  let mut tailCells : List (ℚ × ℚ × Option Found) := []
  if yb && lo < hi then
    match bpCellAt ps geom cpi m' y (min (hi - lo) (1 / 3)) true with
    | some (a, b, f) => tailCells := [(a, b, some f)]; hi := a
    | none => pure ()
  if lo < hi then
    out := out ++ greedyCover ps M geom cpi m' farOk lo hi ((hi - lo) / 16) 400
  return out ++ tailCells

def kindInts : CatalanCore.Uniform.Decay.PolyWire3.CellKind → List Int
  | .base .far => [(0 : Int)]
  | .base (.jetF n lo C Fs) => [(1 : Int), n, lo.num, (lo.den : Int), Fs.num, (Fs.den : Int), C.length] ++
      (C.map pairInts).flatten
  | .base (.mixF n sel ρ lo C Fs eW' eP') => [(2 : Int), n, ρ.num, (ρ.den : Int), lo.num, (lo.den : Int), Fs.num,
      (Fs.den : Int), eW', eP', sel.length] ++ (sel.map fun b => if b then (1 : Int) else 0) ++
      [(C.length : Int)] ++ (C.map pairInts).flatten
  | .bp n side lo C Fs eS => [(3 : Int), n, (if side then 1 else 0), lo.num, (lo.den : Int), Fs.num,
      (Fs.den : Int), eS, C.length] ++ (C.map pairInts).flatten
  | .mp rm rh => [(4 : Int), rm.num, (rm.den : Int), rh.num, (rh.den : Int)]

def showInts (l : List Int) : String := " ".intercalate (l.map toString)

/-! ### cap (upper bounds of g through the negated pieces) -/

def negPs : List WP := psC.map negW

def bestCap (a b : ℚ) (aBp bBp : Bool) : Option (ℚ × Found) := Id.run do
  let (zc, dd, h) := lineGeom a b
  let ps' := negPs
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
  -- breakpoint cells are better next to a breakpoint
  let mut cands : List Found := res.toList
  if aBp then
    for n in [8, 6] do
      match evalBp n false ps' zc dd h 0 with
      | some f => cands := f :: cands
      | none => pure ()
  if bBp then
    for n in [8, 6] do
      match evalBp n true ps' zc dd h 0 with
      | some f => cands := f :: cands
      | none => pure ()
  let mut best : Option (ℚ × Found) := none
  for f in cands do
    let m'' := floorG f.margin (10 ^ 15)
    if checkKind ps' none zc dd h 0 m'' f.kind then
      match best with
      | some (ub, _) => if -m'' < ub then best := some (-m'', f)
      | none => best := some (-m'', f)
  return best

def polyAt (Q : List ℚ) (s : ℚ) : ℚ := (List.range Q.length).foldl (fun acc k => acc + coeffs Q k * s ^ k) 0

/-- PL cap cell: the chord `ua → ub` is a majorant of `g` on `[a, b]` (jet of order 8 for the negated
pieces with a linear shift, `PLKind.lin`); verified by the library Boolean `plUbOk`. -/
def plTry (a b : ℚ) : Option (ℚ × ℚ × ℕ × ℚ × List ℚ × ℚ) :=
  let (zc, dd, h) := lineGeom a b
  match evalJet 8 negPs zc dd h 0 with
  | some f =>
    match f.kind with
    | .base (.jetF n _ C Fs) =>
      let Q := cellPoly C 0 zc dd
      let ga := -(polyAt Q (-h))
      let gb := -(polyAt Q h)
      let build := fun (δ : ℚ) =>
        let ua := ceil18 (ga + δ)
        let ub := ceil18 (gb + δ)
        let lo := loOfNh n (addL Q [(ua + ub) / 2, (ub - ua) / (b - a)]) h
        (ua, ub, lo)
      let (_, _, lo0) := build 0
      let need := Fs + modSum Rtw Wc eWc ePc negPs - lo0
      let δ := if need > 0 then need + 1 / 10 ^ 15 else 0
      let (ua, ub, lo) := build δ
      let x : PLCap := ⟨(a, b, ua, ub), .lin n lo C Fs⟩
      if plUbOk nuC none Rtw eWc ePc Dc x then some (ua, ub, n, lo, C, Fs) else none
    | _ => none
  | none => none

inductive CapR where
  | const (ub : ℚ) (f : Found)
  | lin (ua ub : ℚ) (n : ℕ) (lo : ℚ) (C : List ℚ) (Fs : ℚ)
  | fail

def capCost (a b : ℚ) : CapR → ℚ
  | .const ub _ => (b - a) * max (ub - Dc.mprime) 0
  | .lin ua ub _ _ _ _ => (b - a) * (max (ua - Dc.mprime) 0 + max (ub - Dc.mprime) 0) / 2
  | .fail => 1

def bestCapR (usePL : Bool) (a b : ℚ) (aBp bBp : Bool) : CapR :=
  let c : CapR := match bestCap a b aBp bBp with
    | some (ub, f) => .const ub f
    | none => .fail
  if usePL && decide (a < b) then
    match plTry a b with
    | some (ua, ub, n, lo, C, Fs) =>
      let l : CapR := .lin ua ub n lo C Fs
      if capCost a b l < capCost a b c then l else c
    | none => c
  else c

/-- Greedy cap cover: the widest cell `[a, e]` whose excess `∫ (ub - m')` is at most `τ (e - a)`, where
`τ` is the cap's share of the receipt's excess budget (total cost ≤ τ r₀ ≤ the receipt's `cap_excess`). -/
partial def greedyCap (usePL : Bool) (tau : ℚ) (a b : ℚ) (bpsL : List ℚ) (w : ℚ) (fuel : ℕ) : List (ℚ × ℚ × CapR) :=
  if a ≥ b then [] else
  if fuel = 0 then [(a, b, .fail)] else
  let tr := fun (e : ℚ) =>
    let r := bestCapR usePL a e (bpsL.contains a) (bpsL.contains e)
    match r with
    | .fail => none
    | r => if capCost a e r ≤ tau * (e - a) || e - a < 1 / 10 ^ 13 then some r else none
  match (if b - a ≤ 2 * w then tr b else none) with
  | some r => [(a, b, r)]
  | none =>
    let w0 := if w ≤ 0 || a + w ≥ b then (b - a) / 2 else w
    let rec shrink (w : ℚ) (k : ℕ) : Option (ℚ × CapR) :=
      match k with
      | 0 => none
      | k + 1 =>
        let e := stepTo b a w
        match tr e with
        | some r => some (e, r)
        | none => shrink (w * 2 / 3) k
    match shrink w0 120 with
    | none => [(a, b, .fail)]
    | some (e0, r0) =>
      let rec up (e : ℚ) (r : CapR) (k : ℕ) : (ℚ × CapR) × ℚ :=
        match k with
        | 0 => ((e, r), e)
        | k + 1 =>
          if e ≥ b then ((e, r), e) else
          let e' := stepTo b a ((e - a) * 3 / 2)
          match tr e' with
          | some r' => up e' r' k
          | none => ((e, r), e')
      let ((e1, r1), eb) := up e0 r0 60
      let rec refine (lo : ℚ) (rl : CapR) (hi : ℚ) (k : ℕ) : ℚ × CapR :=
        match k with
        | 0 => (lo, rl)
        | k + 1 =>
          let mid := rbq ((lo + hi) / 2)
          if mid ≤ lo || mid ≥ hi then (lo, rl) else
          match tr mid with
          | some r => refine mid r hi k
          | none => refine lo rl mid k
      let (e2, r2) := if e1 ≥ b then (e1, r1) else refine e1 r1 eb 3
      (a, e2, r2) :: greedyCap usePL tau e2 b bpsL (e2 - a) (fuel - 1)

/-! ### the multipole data -/

def mkM (c : CQ) (K J : ℕ) : Option MPData :=
  let Aabs := ((psC.map fun P : WP => |P.w| * absM P.a).sum * 10 ^ 6).ceil / (10 ^ 6 : ℚ)
  let mx := (psC.flatMap fun P => [(CQ.sub P.A c).nsq, (CQ.sub P.B c).nsq]).foldl max 0
  let R := sqrtHi mx
  let M : MPData := ⟨c, R, K, J, Aabs, momList psC c K⟩
  if mpGlobalOk psC M then some M else none

def mpMain : IO (Option MPData) := pure none

def process (Mopt : Option MPData) (line : String) : IO Unit := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  match ws with
  | ["T", ei] =>
    let e := edgesC.getD ei.toNat! ((0, 0), (0, 0))
    let B := sortQ (([0, 1] ++ edgeBps e).eraseDups)
    let isBp := edgeBps e
    for (x, y) in B.zip B.tail do
      let res := coverSeg psC Mopt (tubeGeom e) cpiC Dc.mprime x y (isBp.contains x) (isBp.contains y)
        (fun a b => cellFarOk Dc Fc e (a, b))
      for (p, q, f) in res do
        match f with
        | some f => IO.println s!"T {ei} {p.num} {p.den} {q.num} {q.den} | {showInts (kindInts f.kind)}"
        | none => IO.println s!"FAIL T {ei} {p.num} {p.den} {q.num} {q.den}"
  | ["L"] =>
    let B := sortQ (([0, 1] ++ realBps 0 1).eraseDups)
    let isBp := realBps 0 1
    for (x, y) in B.zip B.tail do
      let res := coverSeg psC Mopt lineGeom cpiC Dc.gmin x y (isBp.contains x) (isBp.contains y)
        (fun _ _ => false)
      for (p, q, f) in res do
        match f with
        | some f => IO.println s!"L {p.num} {p.den} {q.num} {q.den} | {showInts (kindInts f.kind)}"
        | none => IO.println s!"FAIL L {p.num} {p.den} {q.num} {q.den}"
  | tag :: rest =>
    let tau : ℚ := match rest with
      | [tn, td] => qOf tn td
      | _ => 1 / 100000000000
    if tag == "C" || tag == "CP" then
      let bl := realBps (-Dc.r0) 0
      let B := sortQ (([-Dc.r0, 0] ++ bl).eraseDups)
      for (x, y) in B.zip B.tail do
        for (p, q, r) in greedyCap (tag == "CP") tau x y bl ((y - x) / 16) 400 do
          match r with
          | .const ub f =>
            IO.println s!"C {p.num} {p.den} {q.num} {q.den} | {ub.num} {ub.den} | {showInts (kindInts f.kind)}"
          | .lin ua ub n lo C Fs =>
            IO.println s!"PL {p.num} {p.den} {q.num} {q.den} | {ua.num} {ua.den} {ub.num} {ub.den} | {n} {lo.num} {lo.den} {Fs.num} {Fs.den} {C.length} {showInts ((C.map pairInts).flatten)}"
          | .fail => IO.println s!"FAIL C {p.num} {p.den} {q.num} {q.den}"
  | _ => IO.eprintln s!"bad line {line}"

end GenC

open GenC in
def main (args : List String) : IO Unit := do
  match args with
  | [file, k, nslices] =>
    let lines ← IO.FS.lines file
    -- the multipole line (if any) is applied to every slice
    let mut Mopt : Option MPData := none
    for l in lines do
      let ws := (l.splitOn " ").filter (· ≠ "")
      match ws with
      | ["M", cn, cd, dn, dd, K, J] =>
        Mopt := mkM ⟨qOf cn cd, qOf dn dd⟩ K.toNat! J.toNat!
        match Mopt with
        | some M =>
          if k == "0" then
            IO.println s!"MP {M.c.re.num} {M.c.re.den} {M.c.im.num} {M.c.im.den} {M.R.num} {M.R.den} {M.K} {M.J} {M.Aabs.num} {M.Aabs.den} | {showInts (M.mu.flatMap fun z => pairInts z.re ++ pairInts z.im)}"
        | none => if k == "0" then IO.println "MPNONE"
      | _ => pure ()
    let mut i := 0
    for l in lines do
      if !(l.startsWith "M") then
        if i % nslices.toNat! == k.toNat! then
          process Mopt l
          (← IO.getStdout).flush
        i := i + 1
  | _ => IO.eprintln "usage: GenCover spec k nslices"
