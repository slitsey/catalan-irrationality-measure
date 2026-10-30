import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
/-- No-UF strict envelope min(T, LP, M3D) for the pole index `j = 2`, then zero. -/
noncomputable def profile2 : List Piece := [
  mkPiece 1 9 55 468 (22) (-18) (23400000000) (9),
  mkPiece 55 468 50 423 (55) (378) (117000000000) (45),
  mkPiece 50 423 5 42 (155) (-468) (117000000000) (45),
  mkPiece 5 42 11 90 (22) (-18) (23400000000) (9),
  mkPiece 11 90 10 81 (11) (72) (23400000000) (9),
  mkPiece 10 81 1 8 (31) (-90) (23400000000) (9),
  mkPiece 1 8 55 423 (22) (-18) (23400000000) (9),
  mkPiece 55 423 25 189 (55) (333) (117000000000) (45),
  mkPiece 25 189 5 37 (155) (-423) (117000000000) (45),
  mkPiece 5 37 11 81 (22) (-18) (23400000000) (9),
  mkPiece 11 81 5 36 (11) (63) (23400000000) (9),
  mkPiece 5 36 1 7 (31) (-81) (23400000000) (9),
  mkPiece 1 7 55 378 (22) (-18) (23400000000) (9),
  mkPiece 55 378 50 333 (55) (288) (117000000000) (45),
  mkPiece 50 333 11 72 (155) (-378) (117000000000) (45),
  mkPiece 11 72 5 32 (100) (-18) (117000000000) (45),
  mkPiece 5 32 10 63 (11) (54) (23400000000) (9),
  mkPiece 10 63 55 333 (31) (-72) (23400000000) (9),
  mkPiece 55 333 1 6 (100) (-27) (117000000000) (45),
  mkPiece 1 6 25 144 (55) (243) (117000000000) (45),
  mkPiece 25 144 11 63 (155) (-333) (117000000000) (45),
  mkPiece 11 63 5 27 (100) (-18) (117000000000) (45),
  mkPiece 5 27 55 288 (31) (-63) (23400000000) (9),
  mkPiece 55 288 1 5 (100) (-27) (117000000000) (45),
  mkPiece 1 5 50 243 (55) (198) (117000000000) (45),
  mkPiece 50 243 2 9 (7) (-3) (7800000000) (3),
  mkPiece 2 9 5 22 (29) (-45) (23400000000) (9),
  mkPiece 5 22 11 45 (100) (-27) (117000000000) (45),
  mkPiece 11 45 25 99 (5) (22) (13000000000) (5),
  mkPiece 25 99 5 18 (19) (0) (23400000000) (9),
  mkPiece 5 18 5 17 (29) (-36) (23400000000) (9),
  mkPiece 5 17 11 36 (100) (-27) (117000000000) (45),
  mkPiece 11 36 50 153 (5) (17) (13000000000) (5),
  mkPiece 50 153 1 3 (145) (-153) (117000000000) (45),
  mkPiece 1 3 55 153 (100) (-18) (117000000000) (45),
  mkPiece 55 153 10 27 (1) (3) (2600000000) (1),
  mkPiece 10 27 11 27 (29) (-27) (23400000000) (9),
  mkPiece 11 27 5 12 (2) (0) (2600000000) (1),
  mkPiece 5 12 25 54 (5) (12) (13000000000) (5),
  mkPiece 25 54 1 2 (145) (-108) (117000000000) (45),
  mkPiece 1 2 55 108 (100) (-18) (117000000000) (45),
  mkPiece 55 108 5 9 (1) (2) (2600000000) (1),
  mkPiece 5 9 11 18 (29) (-18) (23400000000) (9),
  mkPiece 11 18 5 7 (2) (0) (2600000000) (1),
  mkPiece 5 7 50 63 (5) (7) (13000000000) (5),
  mkPiece 50 63 1 1 (65) (-42) (39000000000) (15),
  mkPiece 1 1 10 9 (35) (-12) (39000000000) (15),
  mkPiece 10 9 11 9 (155) (-81) (117000000000) (45),
  mkPiece 11 9 5 2 (100) (-36) (117000000000) (45),
  mkPiece 5 2 55 18 (55) (-18) (117000000000) (45),
  mkPiece 55 18 55 9 (0) (0) (2600000000) (1),
  mkPiece 55 9 63 10 (0) (0) (2600000000) (1)]

def profile2Mass : ℚ := (6424577335889 / 2071005928992)
theorem profile2_chain : Chain (1 / 9) profile2 := by
  norm_num [profile2, Chain, mkPiece]
theorem profile2_end : lastEnd (1 / 9) profile2 = (63 / 10) := by
  norm_num [profile2, lastEnd, mkPiece]
theorem profile2_mass : listInt profile2 = (profile2Mass : ℝ) := by
  norm_num [profile2, listInt, Piece.int, profile2Mass, mkPiece]
#print axioms profile2_chain
#print axioms profile2_end
#print axioms profile2_mass
end CatalanCore.Uniform.Bank.FifthsContent
