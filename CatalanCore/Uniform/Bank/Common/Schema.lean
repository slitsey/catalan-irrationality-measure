module

public import CatalanCore.Uniform.Decay.Cert.Data
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

/-!
# Bank data schema (lane B, package B0)

Decoders from `raw_ints%` integer tapes to the rational data of a hybrid bank.  All rationals are
stored as consecutive pairs `(numerator, denominator)`; all decoders are structural recursions on the tape.

* `Seg` tape: `tau, ax(2), ay(2), bx(2), by(2), M(2), Lq(2), coef(2 each)...`
* cover cell tape: `a(2), b(2)` per cell; info tape: `a(2), b(2), rule, lo(2), hi(2)` per cell
* frame/geometry/polygon: pairs, see `FrameMember`, `GeomData`, `PolygonData`.
-/

namespace CatalanCore.Uniform.Bank.Common

open CatalanCore.Uniform.Decay.Cert

/-- Rationals from consecutive `(n, d)` pairs. -/
def ratsOf : List ℤ → List ℚ
  | n :: d :: t => ((n : ℚ) / (d : ℚ)) :: ratsOf t
  | _ => []

/-- One rational from an `[n, d]` tape. -/
def q1 (t : List ℤ) : ℚ := (ratsOf t).headD 0

/-- Pairs of consecutive rationals. -/
def pairsOf : List ℚ → List (ℚ × ℚ)
  | a :: b :: t => (a, b) :: pairsOf t
  | _ => []

/-- Triples of consecutive rationals. -/
def triplesOf : List ℚ → List (ℚ × ℚ × ℚ)
  | a :: b :: c :: t => (a, b, c) :: triplesOf t
  | _ => []

/-- A segment from its tape. -/
def decodeSeg : List ℤ → Seg
  | tau :: t =>
    let r := ratsOf t
    { ax := r.getD 0 0, ay := r.getD 1 0, bx := r.getD 2 0, byy := r.getD 3 0,
      coef := r.drop 6, M := r.getD 4 0, Lq := r.getD 5 0, tau := tau.toNat }
  | [] => { ax := 0, ay := 0, bx := 0, byy := 0, coef := [], M := 0, Lq := 0, tau := 0 }

/-- Cover cells `(a, b)`. -/
def cellsOf (t : List ℤ) : List (ℚ × ℚ) := pairsOf (ratsOf t)

/-- Per-cell receipt data. -/
structure CellInfo where
  a : ℚ
  b : ℚ
  /-- 0: endpoint rule, 1: order-8 log jet rule -/
  rule : ℕ
  lo : ℚ
  hi : ℚ

/-- Info cells from a tape of 9 integers per cell. -/
def infoOf : List ℤ → List CellInfo
  | a1 :: a2 :: b1 :: b2 :: ru :: l1 :: l2 :: h1 :: h2 :: t =>
    { a := (a1 : ℚ) / a2, b := (b1 : ℚ) / b2, rule := ru.toNat, lo := (l1 : ℚ) / l2,
      hi := (h1 : ℚ) / h2 } :: infoOf t
  | _ => []

/-- A frame member: poles at `-(n + shift)` with coefficients (sum zero). -/
structure FrameMember where
  shifts : List ℚ
  coeffs : List ℚ

/-- Block geometry: the alternating geometry with parameter `alpha`; blocks are `(lo, hi, density)`. -/
structure GeomData where
  alpha : ℚ
  dim : ℕ
  selectorPair : Bool
  rows : List (ℚ × ℚ × ℚ)
  cols : List (ℚ × ℚ × ℚ)

/-- Contour polygon: base vertex `(-r0, 0)` first; NW tail of direction `-1 + i s`. -/
structure PolygonData where
  vertices : List (ℚ × ℚ)
  tailSlope : ℚ
  tailLean : ℚ

/-- Blocks `(lo, hi, density)` from a tape. -/
def blocksOf (t : List ℤ) : List (ℚ × ℚ × ℚ) := triplesOf (ratsOf t)

/-- Polygon vertices from a tape. -/
def vertsOf (t : List ℤ) : List (ℚ × ℚ) := pairsOf (ratsOf t)

end CatalanCore.Uniform.Bank.Common
