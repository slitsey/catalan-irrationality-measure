module

public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# Piece tables of the thirds frames (data)

`tlow` (`3 kq ≈ p`, kappa = 1/3) and `thigh` (`3 kq ≈ 2p`, kappa = 2/3): the M0 tables with additive
constant `C = 6` (window `r ≤ 8m ≤ r + 9`), the first piece realised by `D1x` with `n = 0`, and a final
tail piece `(15/4, 4]` resp. `(15/8, 4]` with weight `≤ 6`.  Both chains start at `1/4` (after `ld1`)
and end at `4`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.Thirds

noncomputable def tlow : List Piece :=
  [mkPiece 1 4 27 32 17 0 48 8, mkPiece 27 32 15 16 39 (-16) 72 12,
   mkPiece 15 16 1 1 27 (-16) 36 6, mkPiece 1 1 5 4 21 (-10) 36 6,
   mkPiece 5 4 3 1 27 (-8) 72 12, mkPiece 3 1 15 4 15 (-4) 72 12,
   mkPiece 15 4 4 1 0 0 6 1]

noncomputable def thigh : List Piece :=
  [mkPiece 1 4 27 40 17 0 48 8, mkPiece 27 40 3 4 39 (-20) 72 12,
   mkPiece 3 4 1 1 27 (-20) 36 6, mkPiece 1 1 5 4 21 (-14) 36 6,
   mkPiece 5 4 3 2 27 (-16) 72 12, mkPiece 3 2 15 8 15 (-8) 72 12,
   mkPiece 15 8 4 1 0 0 6 1]

lemma tlow_chain : Chain (1 / 4) tlow := by
  simp only [tlow, Chain, mkPiece]
  norm_num

lemma thigh_chain : Chain (1 / 4) thigh := by
  simp only [thigh, Chain, mkPiece]
  norm_num

lemma tlow_end : lastEnd (1 / 4) tlow = 4 := by
  simp [tlow, lastEnd, mkPiece]

lemma thigh_end : lastEnd (1 / 4) thigh = 4 := by
  simp [thigh, lastEnd, mkPiece]

lemma llow_chain : Chain (1 / 68) (ld1 ++ tlow) := by
  rw [chain_append, ld1_end]; exact ⟨ld1_chain, tlow_chain⟩

lemma lhigh_chain : Chain (1 / 68) (ld1 ++ thigh) := by
  rw [chain_append, ld1_end]; exact ⟨ld1_chain, thigh_chain⟩

lemma llow_end : lastEnd (1 / 68) (ld1 ++ tlow) = 4 := by
  rw [lastEnd_append, ld1_end, tlow_end]

lemma lhigh_end : lastEnd (1 / 68) (ld1 ++ thigh) = 4 := by
  rw [lastEnd_append, ld1_end, thigh_end]

/-- Class constant of the low class (`φ(6) = 2`). -/
noncomputable def Clow : ℝ := (9 / 4 * (1 / 68) + listInt (ld1 ++ tlow)) / 2
/-- Class constant of the high class. -/
noncomputable def Chigh : ℝ := (9 / 4 * (1 / 68) + listInt (ld1 ++ thigh)) / 2

/-- The content constant of the thirds frames (tropical): `3.2312582 ≤ 32313/10000`. -/
theorem Clow_add_Chigh_le : Clow + Chigh ≤ 32313 / 10000 := by
  simp only [Clow, Chigh, listInt_append, ld1, tlow, thigh, listInt, Piece.int, mkPiece]
  norm_num

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.Clow_add_Chigh_le
