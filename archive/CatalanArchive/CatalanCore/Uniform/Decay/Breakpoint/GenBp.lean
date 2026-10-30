import CatalanCore.Uniform.Bank.Chi3.Env
import CatalanCore.Uniform.Decay.Breakpoint.Cell
set_option Elab.async false
set_option maxRecDepth 100000

/-! Scratch (D14): data generator for the breakpoint-cell pilots on Chi3. Not part of the library. -/

namespace CatalanCore.Uniform.Decay.Breakpoint.GenBp
open CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.NearFast CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Spline

def fl (q : ℚ) : Float := Float.ofInt ((q * 10 ^ 30).floor) / 1e30
def ceil18 (F : ℚ) : ℚ := ((F * 10 ^ 18).ceil : ℤ) / (10 ^ 18 : ℚ)
/-- Round down to the odd grid `3^-40` (de-structures 2-adic denominators). -/
def rb (q : ℚ) : ℚ := (⌊q * 3 ^ 40⌋ : ℤ) / (3 ^ 40 : ℚ)
def litQ (q : ℚ) : String := s!"(({q.num} : ℤ) : ℚ) / {q.den}"
def litL (l : List ℚ) : String := "[" ++ String.intercalate ", " (l.map litQ) ++ "]"
def minE (f : ℕ → Bool) : ℕ := (List.range 200).find? f |>.getD 200

def loOfN (n : ℕ) (C : List ℚ) (S : ℚ) : ℚ :=
  let bs := (List.range n).map fun k => bernK (affK (coeffs C) (n - 1) 0 S) (n - 1) k
  let m := bs.foldl min (bs.headD 0)
  (⌊m * 10 ^ 18⌋ : ℤ) / (10 ^ 18 : ℚ)

def theps : List WP := cellPieces Dn nuC

structure Res where
  ulo : ℚ
  uhi : ℚ
  zc : CQ
  dd : CQ
  h : ℚ
  C : List ℚ
  lo : ℚ
  Fs : ℚ
  eS : ℕ
  margin : ℚ
  Ff : ℚ
  Fi : ℚ
  logb : ℚ
  Cf : List ℚ
  Ci : List ℚ
  Bi : List ℚ

def evalBp (ei : ℕ) (up : ℚ) (side : Bool) (L : ℚ) (n : ℕ) : Option Res :=
  let e := edgesLit[ei]!
  let ulo := if side then up - L else up
  let uhi := if side then up else up + L
  let a := cqOf e.1
  let b := cqOf e.2
  let zc := edgeCentre a b ulo uhi
  let dd := CQ.sub b a
  let h := (uhi - ulo) / 2
  let p := bpPoint side zc dd h
  let d' := bpDir side dd
  let S := 2 * h
  match aggEvalMF n p d' S (bpFar p theps), incAgg n d' S (bpInc p theps) with
  | some (Cf, Ff), some (Ci, Bi, Fi) =>
    let C := addL Cf Ci
    let eS := minE (fun k => decide (1 ≤ S * 2 ^ k))
    let logb := lsum (fun m => |coeffs Bi m| * S ^ m) n * (eS * (7 / 10))
    let Fs := ceil18 (Ff + Fi + logb)
    let lo := loOfN n (cellPoly C (cpiOf Dn) p d') S
    let margin := lo - Fs - modSum Rtw Dn.W eWc ePc theps - Dn.mprime
    some ⟨ulo, uhi, zc, dd, h, C, lo, Fs, eS, margin, Ff, Fi, logb, Cf, Ci, Bi⟩
  | _, _ => none

def okMargin (r : Option Res) : Bool :=
  match r with
  | some x => decide (1 / 10 ^ 7 ≤ x.margin)
  | none => false

/-- Largest feasible `L` below `Lmax` on the ladder `Lmax (9/10)^k`, refined by bisection. -/
def findL (ei : ℕ) (up : ℚ) (side : Bool) (n : ℕ) (Lmax : ℚ) : ℚ :=
  let ok := fun L => okMargin (evalBp ei up side L n)
  match (List.range 150).find? (fun k => ok (rb (Lmax * (9 / 10) ^ k))) with
  | none => 0
  | some 0 => rb Lmax
  | some k =>
    let hi0 := rb (Lmax * (9 / 10) ^ (k - 1))
    let lo0 := rb (Lmax * (9 / 10) ^ k)
    let st : ℚ × ℚ := (List.range 8).foldl (fun (lo, hi) _ =>
      let mid := rb ((lo + hi) / 2)
      if ok mid then (mid, hi) else (lo, mid)) (lo0, hi0)
    st.1

def report (ei : ℕ) (up : ℚ) (side : Bool) (n : ℕ) (L : ℚ) : String :=
  match evalBp ei up side L n with
  | some r =>
    s!"e{ei} up={fl up} side={side} L={fl L} margin={fl r.margin} lo={fl r.lo} Ff={fl r.Ff} Fi={fl r.Fi} logb={fl r.logb} eS={r.eS} C0={fl (r.C.headD 0)} C1={fl (r.C.getD 1 0)} Bi={r.Bi.map fl}"
  | none => s!"e{ei} up={fl up} side={side} L={fl L}: none"

def thm (name : String) (ei : ℕ) (up : ℚ) (side : Bool) (n : ℕ) (L : ℚ) : String :=
  match evalBp ei up side L n with
  | some r =>
    s!"-- {name}: margin {fl r.margin}\ntheorem {name} : bpOk {n} {side} theps (edgeCentre (cqOf e{ei}.1) (cqOf e{ei}.2) ({litQ r.ulo}) ({litQ r.uhi})) (CQ.sub (cqOf e{ei}.2) (cqOf e{ei}.1)) ((({litQ r.uhi}) - ({litQ r.ulo})) / 2) Dn.W Rtw (cpiOf Dn) ({litQ r.lo}) Dn.mprime {litL r.C} ({litQ r.Fs}) eWc ePc {r.eS} = true := by decide +kernel"
  | none => s!"-- {name} none"

def onEdge (e : Pt × Pt) (x : CQ) : Option ℚ :=
  let a := cqOf e.1
  let b := cqOf e.2
  let d := CQ.sub b a
  let u := if d.re ≠ 0 then (x.re - a.re) / d.re else (x.im - a.im) / d.im
  if x.re = a.re + u * d.re ∧ x.im = a.im + u * d.im ∧ 0 ≤ u ∧ u ≤ 1 then some u else none

def bps (e : Pt × Pt) : List ℚ :=
  (((cellPieces Dn nuC).flatMap fun P => [onEdge e P.A, onEdge e P.B]).filterMap id).eraseDups

end CatalanCore.Uniform.Decay.Breakpoint.GenBp
