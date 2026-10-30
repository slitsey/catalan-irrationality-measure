import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
/-- No-UF strict envelope min(T, LP, M3D) for the pole index `j = 4`, then zero. -/
noncomputable def profile4 : List Piece := [
  mkPiece 1 9 55 486 (22) (-18) (23400000000) (9),
  mkPiece 55 486 50 441 (55) (396) (117000000000) (45),
  mkPiece 50 441 5 44 (155) (-486) (117000000000) (45),
  mkPiece 5 44 11 90 (22) (-18) (23400000000) (9),
  mkPiece 11 90 10 81 (11) (72) (23400000000) (9),
  mkPiece 10 81 55 441 (31) (-90) (23400000000) (9),
  mkPiece 55 441 1 8 (100) (-9) (117000000000) (45),
  mkPiece 1 8 25 198 (55) (351) (117000000000) (45),
  mkPiece 25 198 5 39 (155) (-441) (117000000000) (45),
  mkPiece 5 39 11 81 (22) (-18) (23400000000) (9),
  mkPiece 11 81 5 36 (11) (63) (23400000000) (9),
  mkPiece 5 36 50 351 (7) (-3) (7800000000) (3),
  mkPiece 50 351 5 34 (155) (-396) (117000000000) (45),
  mkPiece 5 34 11 72 (22) (-18) (23400000000) (9),
  mkPiece 11 72 10 63 (11) (54) (23400000000) (9),
  mkPiece 10 63 25 153 (7) (-3) (7800000000) (3),
  mkPiece 25 153 5 29 (155) (-351) (117000000000) (45),
  mkPiece 5 29 11 63 (22) (-18) (23400000000) (9),
  mkPiece 11 63 5 27 (11) (45) (23400000000) (9),
  mkPiece 5 27 50 261 (7) (-3) (7800000000) (3),
  mkPiece 50 261 11 54 (155) (-306) (117000000000) (45),
  mkPiece 11 54 5 24 (100) (-36) (117000000000) (45),
  mkPiece 5 24 2 9 (11) (36) (23400000000) (9),
  mkPiece 2 9 25 108 (19) (0) (23400000000) (9),
  mkPiece 25 108 1 4 (145) (-216) (117000000000) (45),
  mkPiece 1 4 55 216 (100) (-36) (117000000000) (45),
  mkPiece 55 216 5 18 (1) (4) (2600000000) (1),
  mkPiece 5 18 50 171 (19) (0) (23400000000) (9),
  mkPiece 50 171 55 171 (145) (-171) (117000000000) (45),
  mkPiece 55 171 1 3 (2) (0) (2600000000) (1),
  mkPiece 1 3 10 27 (1) (3) (2600000000) (1),
  mkPiece 10 27 25 63 (19) (0) (23400000000) (9),
  mkPiece 25 63 55 126 (145) (-126) (117000000000) (45),
  mkPiece 55 126 1 2 (2) (0) (2600000000) (1),
  mkPiece 1 2 5 9 (1) (2) (2600000000) (1),
  mkPiece 5 9 11 18 (100) (-9) (117000000000) (45),
  mkPiece 11 18 50 81 (5) (9) (13000000000) (5),
  mkPiece 50 81 1 1 (65) (-54) (39000000000) (15),
  mkPiece 1 1 10 9 (35) (-24) (39000000000) (15),
  mkPiece 10 9 11 9 (155) (-117) (117000000000) (45),
  mkPiece 11 9 5 4 (100) (-72) (117000000000) (45),
  mkPiece 5 4 55 36 (55) (-36) (117000000000) (45),
  mkPiece 55 36 55 9 (0) (0) (2600000000) (1),
  mkPiece 55 9 63 10 (0) (0) (2600000000) (1)]

def profile4Mass : ℚ := (2513881161109 / 1435428024030)
theorem profile4_chain : Chain (1 / 9) profile4 := by
  norm_num [profile4, Chain, mkPiece]
theorem profile4_end : lastEnd (1 / 9) profile4 = (63 / 10) := by
  norm_num [profile4, lastEnd, mkPiece]
theorem profile4_mass : listInt profile4 = (profile4Mass : ℝ) := by
  norm_num [profile4, listInt, Piece.int, profile4Mass, mkPiece]
#print axioms profile4_chain
#print axioms profile4_end
#print axioms profile4_mass
end CatalanCore.Uniform.Bank.FifthsContent
