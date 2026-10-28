import CatalanCore.Uniform.Decay.PolyWire2.Top2
import CatalanMeasure.CellCert.RawInts
set_option Elab.async false

/-!
# Decoders and cons lemmas for the per-cell data (lane B, package B3b)

Cells are stored as `raw_ints%` tapes: `ulo(2), uhi(2)` then the kind:
`0` far; `1 n lo(2) Fs(2) len C(2 len)` for `jetF`; `2 n ρ(2) lo(2) Fs(2) eW' eP' ns sel(ns) len C(2 len)`
for `mixF`.  All decoders are structural.
-/

namespace CatalanCore.Uniform.Decay.PolyWire2

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells

/-- Rationals from consecutive `(n, d)` pairs. -/
def qsOf : List ℤ → List ℚ
  | n :: d :: t => ((n : ℚ) / (d : ℚ)) :: qsOf t
  | _ => []

/-- Pairs of consecutive rationals. -/
def pairsQ : List ℚ → List (ℚ × ℚ)
  | a :: b :: t => (a, b) :: pairsQ t
  | _ => []

def qOfP (n d : ℤ) : ℚ := (n : ℚ) / (d : ℚ)

def decodeKind : List ℤ → CellKind2
  | 1 :: n :: ln :: ld :: fn :: fd :: len :: t =>
      .jetF n.toNat (qOfP ln ld) (qsOf (t.take (2 * len.toNat))) (qOfP fn fd)
  | 2 :: n :: rn :: rd :: ln :: ld :: fn :: fd :: ew :: ep :: ns :: t =>
      match t.drop ns.toNat with
      | len :: t' =>
          .mixF n.toNat ((t.take ns.toNat).map fun b => decide (b = 1)) (qOfP rn rd) (qOfP ln ld)
            (qsOf (t'.take (2 * len.toNat))) (qOfP fn fd) ew.toNat ep.toNat
      | [] => .far
  | _ => .far

def decodeCell : List ℤ → TCell2
  | un :: ud :: vn :: vd :: k => ⟨qOfP un ud, qOfP vn vd, decodeKind k⟩
  | _ => ⟨0, 0, .far⟩

/-- A cap cell: tape `ulo(2) uhi(2) kind...` with the upper bound as a separate pair. -/
def decodeCap (ub : List ℤ) (t : List ℤ) : TCell2 × ℚ :=
  (decodeCell t, (qsOf ub).headD 0)

theorem allT_nil {α : Type} (f : α → Bool) : ([] : List α).all f = true := rfl

theorem allT_cons {α : Type} {f : α → Bool} {a : α} {l : List α} (h : f a = true)
    (hl : l.all f = true) : (a :: l).all f = true := by
  simp [List.all_cons, h, hl]

theorem allT_append {α : Type} {f : α → Bool} {l1 l2 : List α} (h1 : l1.all f = true)
    (h2 : l2.all f = true) : (l1 ++ l2).all f = true := by
  simp [List.all_append, h1, h2]

theorem tubeCells2_nil (ok : Pt × Pt → TCell2 → Bool) : tubeCells2 ok [] [] = true := rfl

theorem tubeCells2_cons {ok : Pt × Pt → TCell2 → Bool} {e : Pt × Pt} {cs : List TCell2}
    {es : List (Pt × Pt)} {css : List (List TCell2)} (h1 : edgeCells2 ok e cs = true)
    (h2 : tubeCells2 ok es css = true) : tubeCells2 ok (e :: es) (cs :: css) = true := by
  simp [tubeCells2, h1, h2]

theorem edgeCells2_of {ok : Pt × Pt → TCell2 → Bool} {e : Pt × Pt} {cs : List TCell2}
    (h1 : coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) = true) (h2 : cs.all (ok e) = true) :
    edgeCells2 ok e cs = true := by
  simp [edgeCells2, h1, h2]

end CatalanCore.Uniform.Decay.PolyWire2
