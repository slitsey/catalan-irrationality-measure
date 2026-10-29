import CatalanCore.Uniform.Decay.PolyWire3.Top
import CatalanCore.Uniform.Decay.PolyWire2.Decode
set_option Elab.async false

/-!
# Decoders and cons lemmas for the unified cell tables (lane D, package D17)

Cells are `raw_ints%` tapes: `ulo(2), uhi(2)` then the kind:
`0` far; `1 n lo(2) Fs(2) len C(2 len)` jet; `2 n ρ(2) lo(2) Fs(2) eW' eP' ns sel(ns) len C(2 len)` mix;
`3 n side lo(2) Fs(2) eS len C(2 len)` breakpoint; `4 rm(2) rh(2)` multipole;
`5 len ix(len) body`: the kind `body` (tags `0`–`4`) on the pieces with those at the indices `ix`
reversed (`CellKind.flip`).
A PL cap cell is `tag a(2) b(2) ua(2) ub(2) body`: tag `0` is the constant upper bound `ua` of the
cell kind `body`, tag `1` is the chord `ua → ub` with body `n lo(2) Fs(2) len C(2 len)`.
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.PolyWire2
open CatalanCore.Uniform.Decay.FarField (MPData)
open CatalanCore.Uniform.Decay.NearCells

/-- The kinds of tags `0`–`4`. -/
def decodeKindB : List ℤ → CellKind
  | 3 :: n :: sd :: ln :: ld :: fn :: fd :: es :: len :: t =>
      .bp n.toNat (decide (sd = 1)) (qOfP ln ld) (qsOf (t.take (2 * len.toNat))) (qOfP fn fd) es.toNat
  | 4 :: rmn :: rmd :: rhn :: rhd :: _ => .mp (qOfP rmn rmd) (qOfP rhn rhd)
  | k => .base (decodeKind k)

/-- All kinds: tag `5` is a flip mask in front of a kind of tags `0`–`4`. -/
def decodeKind3 : List ℤ → CellKind
  | 5 :: len :: t => .flip ((t.take len.toNat).map Int.toNat) (decodeKindB (t.drop len.toNat))
  | k => decodeKindB k

def decodeCell3 : List ℤ → TCell
  | un :: ud :: vn :: vd :: k => ⟨qOfP un ud, qOfP vn vd, decodeKind3 k⟩
  | _ => ⟨0, 0, .base .far⟩

/-- A cap cell with a constant upper bound: separate pair for `ub`. -/
def decodeCap3 (ub : List ℤ) (t : List ℤ) : TCell × ℚ :=
  (decodeCell3 t, (qsOf ub).headD 0)

/-- A PL cap cell from its tape. -/
def decodePL : List ℤ → PLCap
  | 0 :: an :: ad :: bn :: bd :: uan :: uad :: _ :: _ :: body =>
      PLCap.ofConst (⟨qOfP an ad, qOfP bn bd, decodeKind3 body⟩, qOfP uan uad)
  | 1 :: an :: ad :: bn :: bd :: uan :: uad :: ubn :: ubd :: n :: ln :: ld :: fn :: fd :: len :: t =>
      ⟨(qOfP an ad, qOfP bn bd, qOfP uan uad, qOfP ubn ubd),
        .lin n.toNat (qOfP ln ld) (qsOf (t.take (2 * len.toNat))) (qOfP fn fd)⟩
  | _ => PLCap.ofConst (⟨0, 0, .base .far⟩, 0)

/-- Complex numbers from consecutive `(re_n, re_d, im_n, im_d)` quadruples. -/
def cqsOf : List ℤ → List CQ
  | a :: b :: c :: d :: t => ⟨qOfP a b, qOfP c d⟩ :: cqsOf t
  | _ => []

theorem tubeCells_nil (ok : Pt × Pt → TCell → Bool) : tubeCells ok [] [] = true := rfl

theorem tubeCells_cons {ok : Pt × Pt → TCell → Bool} {e : Pt × Pt} {cs : List TCell}
    {es : List (Pt × Pt)} {css : List (List TCell)} (h1 : edgeCells ok e cs = true)
    (h2 : tubeCells ok es css = true) : tubeCells ok (e :: es) (cs :: css) = true := by
  simp [tubeCells, h1, h2]

theorem edgeCells_of {ok : Pt × Pt → TCell → Bool} {e : Pt × Pt} {cs : List TCell}
    (h1 : coverOk 0 1 (cs.map fun c => (c.ulo, c.uhi)) = true) (h2 : cs.all (ok e) = true) :
    edgeCells ok e cs = true := by
  simp [edgeCells, h1, h2]

end CatalanCore.Uniform.Decay.PolyWire3
