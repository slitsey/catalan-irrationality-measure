import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
/-- No-UF strict envelope min(T, LP, M3D) for the pole index `j = 3`, then zero. -/
noncomputable def profile3 : List Piece := [
  mkPiece 1 9 55 477 (22) (-18) (23400000000) (9),
  mkPiece 55 477 25 216 (55) (387) (117000000000) (45),
  mkPiece 25 216 5 43 (155) (-477) (117000000000) (45),
  mkPiece 5 43 11 90 (22) (-18) (23400000000) (9),
  mkPiece 11 90 10 81 (11) (72) (23400000000) (9),
  mkPiece 10 81 1 8 (31) (-90) (23400000000) (9),
  mkPiece 1 8 55 432 (22) (-18) (23400000000) (9),
  mkPiece 55 432 50 387 (55) (342) (117000000000) (45),
  mkPiece 50 387 5 38 (155) (-432) (117000000000) (45),
  mkPiece 5 38 11 81 (22) (-18) (23400000000) (9),
  mkPiece 11 81 5 36 (11) (63) (23400000000) (9),
  mkPiece 5 36 55 387 (31) (-81) (23400000000) (9),
  mkPiece 55 387 1 7 (100) (-18) (117000000000) (45),
  mkPiece 1 7 25 171 (55) (297) (117000000000) (45),
  mkPiece 25 171 5 33 (155) (-387) (117000000000) (45),
  mkPiece 5 33 11 72 (22) (-18) (23400000000) (9),
  mkPiece 11 72 10 63 (11) (54) (23400000000) (9),
  mkPiece 10 63 55 342 (31) (-72) (23400000000) (9),
  mkPiece 55 342 1 6 (100) (-18) (117000000000) (45),
  mkPiece 1 6 50 297 (55) (252) (117000000000) (45),
  mkPiece 50 297 11 63 (155) (-342) (117000000000) (45),
  mkPiece 11 63 5 28 (100) (-27) (117000000000) (45),
  mkPiece 5 28 5 27 (11) (45) (23400000000) (9),
  mkPiece 5 27 25 126 (7) (-3) (7800000000) (3),
  mkPiece 25 126 11 54 (155) (-297) (117000000000) (45),
  mkPiece 11 54 5 23 (100) (-27) (117000000000) (45),
  mkPiece 5 23 2 9 (11) (36) (23400000000) (9),
  mkPiece 2 9 50 207 (19) (0) (23400000000) (9),
  mkPiece 50 207 1 4 (145) (-207) (117000000000) (45),
  mkPiece 1 4 55 207 (100) (-27) (117000000000) (45),
  mkPiece 55 207 5 18 (1) (4) (2600000000) (1),
  mkPiece 5 18 11 36 (100) (-18) (117000000000) (45),
  mkPiece 11 36 25 81 (5) (18) (13000000000) (5),
  mkPiece 25 81 1 3 (145) (-162) (117000000000) (45),
  mkPiece 1 3 55 162 (100) (-27) (117000000000) (45),
  mkPiece 55 162 10 27 (1) (3) (2600000000) (1),
  mkPiece 10 27 5 13 (29) (-27) (23400000000) (9),
  mkPiece 5 13 11 27 (100) (-18) (117000000000) (45),
  mkPiece 11 27 50 117 (5) (13) (13000000000) (5),
  mkPiece 50 117 55 117 (145) (-117) (117000000000) (45),
  mkPiece 55 117 1 2 (2) (0) (2600000000) (1),
  mkPiece 1 2 5 9 (1) (2) (2600000000) (1),
  mkPiece 5 9 11 18 (29) (-18) (23400000000) (9),
  mkPiece 11 18 5 8 (2) (0) (2600000000) (1),
  mkPiece 5 8 25 36 (5) (8) (13000000000) (5),
  mkPiece 25 36 1 1 (65) (-48) (39000000000) (15),
  mkPiece 1 1 10 9 (35) (-18) (39000000000) (15),
  mkPiece 10 9 11 9 (155) (-99) (117000000000) (45),
  mkPiece 11 9 5 3 (100) (-54) (117000000000) (45),
  mkPiece 5 3 55 27 (55) (-27) (117000000000) (45),
  mkPiece 55 27 55 9 (0) (0) (2600000000) (1),
  mkPiece 55 9 63 10 (0) (0) (2600000000) (1)]

def profile3Mass : ℚ := (253788527311591 / 116280623178720)
theorem profile3_chain : Chain (1 / 9) profile3 := by
  norm_num [profile3, Chain, mkPiece]
theorem profile3_end : lastEnd (1 / 9) profile3 = (63 / 10) := by
  norm_num [profile3, lastEnd, mkPiece]
theorem profile3_mass : listInt profile3 = (profile3Mass : ℝ) := by
  norm_num [profile3, listInt, Piece.int, profile3Mass, mkPiece]
#print axioms profile3_chain
#print axioms profile3_end
#print axioms profile3_mass
end CatalanCore.Uniform.Bank.FifthsContent
