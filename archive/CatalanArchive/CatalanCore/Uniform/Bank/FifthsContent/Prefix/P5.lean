import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix5 : List Piece := [
  mkPiece 2 315 1 153 (19) (153) (23400000000) (9),
  mkPiece 1 153 2 297 (7) (-51) (7800000000) (3),
  mkPiece 2 297 1 144 (19) (144) (23400000000) (9),
  mkPiece 1 144 2 279 (7) (-48) (7800000000) (3),
  mkPiece 2 279 1 135 (19) (135) (23400000000) (9),
  mkPiece 1 135 2 261 (7) (-45) (7800000000) (3),
  mkPiece 2 261 1 126 (19) (126) (23400000000) (9),
  mkPiece 1 126 2 243 (7) (-42) (7800000000) (3),
  mkPiece 2 243 1 117 (19) (117) (23400000000) (9),
  mkPiece 1 117 2 225 (7) (-39) (7800000000) (3),
  mkPiece 2 225 1 108 (19) (108) (23400000000) (9),
  mkPiece 1 108 2 207 (7) (-36) (7800000000) (3),
  mkPiece 2 207 1 99 (19) (99) (23400000000) (9),
  mkPiece 1 99 2 189 (7) (-33) (7800000000) (3),
  mkPiece 2 189 1 90 (19) (90) (23400000000) (9),
  mkPiece 1 90 2 171 (7) (-30) (7800000000) (3),
  mkPiece 2 171 1 81 (19) (81) (23400000000) (9),
  mkPiece 1 81 2 153 (7) (-27) (7800000000) (3),
  mkPiece 2 153 1 72 (19) (72) (23400000000) (9),
  mkPiece 1 72 2 135 (7) (-24) (7800000000) (3),
  mkPiece 2 135 1 63 (19) (63) (23400000000) (9),
  mkPiece 1 63 2 117 (7) (-21) (7800000000) (3),
  mkPiece 2 117 1 54 (19) (54) (23400000000) (9),
  mkPiece 1 54 2 99 (7) (-18) (7800000000) (3),
  mkPiece 2 99 1 45 (19) (45) (23400000000) (9),
  mkPiece 1 45 2 81 (7) (-15) (7800000000) (3),
  mkPiece 2 81 1 36 (19) (36) (23400000000) (9),
  mkPiece 1 36 2 63 (7) (-12) (7800000000) (3),
  mkPiece 2 63 1 27 (19) (27) (23400000000) (9),
  mkPiece 1 27 2 45 (7) (-9) (7800000000) (3),
  mkPiece 2 45 1 18 (19) (18) (23400000000) (9),
  mkPiece 1 18 2 27 (7) (-6) (7800000000) (3),
  mkPiece 2 27 1 9 (19) (9) (23400000000) (9)]

def prefix5Mass : ℚ := (9473372621996639 / 40938407245335600)
theorem prefix5_chain : Chain (2 / 315) prefix5 := by
  norm_num [prefix5, Chain, mkPiece]
theorem prefix5_end : lastEnd (2 / 315) prefix5 = (1 / 9) := by
  norm_num [prefix5, lastEnd, mkPiece]
theorem prefix5_mass : listInt prefix5 = (prefix5Mass : ℝ) := by
  norm_num [prefix5, listInt, Piece.int, prefix5Mass, mkPiece]
#print axioms prefix5_chain
#print axioms prefix5_end
#print axioms prefix5_mass
end CatalanCore.Uniform.Bank.FifthsContent
