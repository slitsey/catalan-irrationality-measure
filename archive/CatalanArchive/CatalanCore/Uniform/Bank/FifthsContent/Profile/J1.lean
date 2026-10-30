import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
/-- No-UF strict envelope min(T, LP, M3D) for the pole index `j = 1`, then zero. -/
noncomputable def profile1 : List Piece := [
  mkPiece 1 9 55 459 (22) (-18) (23400000000) (9),
  mkPiece 55 459 25 207 (55) (369) (117000000000) (45),
  mkPiece 25 207 5 41 (155) (-459) (117000000000) (45),
  mkPiece 5 41 11 90 (22) (-18) (23400000000) (9),
  mkPiece 11 90 10 81 (11) (72) (23400000000) (9),
  mkPiece 10 81 1 8 (31) (-90) (23400000000) (9),
  mkPiece 1 8 55 414 (22) (-18) (23400000000) (9),
  mkPiece 55 414 50 369 (55) (324) (117000000000) (45),
  mkPiece 50 369 11 81 (155) (-414) (117000000000) (45),
  mkPiece 11 81 5 36 (100) (-9) (117000000000) (45),
  mkPiece 5 36 1 7 (31) (-81) (23400000000) (9),
  mkPiece 1 7 55 369 (22) (-18) (23400000000) (9),
  mkPiece 55 369 25 162 (55) (279) (117000000000) (45),
  mkPiece 25 162 10 63 (7) (-3) (7800000000) (3),
  mkPiece 10 63 1 6 (31) (-72) (23400000000) (9),
  mkPiece 1 6 55 324 (22) (-18) (23400000000) (9),
  mkPiece 55 324 50 279 (55) (234) (117000000000) (45),
  mkPiece 50 279 5 27 (7) (-3) (7800000000) (3),
  mkPiece 5 27 55 279 (31) (-63) (23400000000) (9),
  mkPiece 55 279 1 5 (100) (-36) (117000000000) (45),
  mkPiece 1 5 25 117 (55) (189) (117000000000) (45),
  mkPiece 25 117 2 9 (7) (-3) (7800000000) (3),
  mkPiece 2 9 5 21 (29) (-45) (23400000000) (9),
  mkPiece 5 21 11 45 (100) (-36) (117000000000) (45),
  mkPiece 11 45 50 189 (5) (21) (13000000000) (5),
  mkPiece 50 189 5 18 (19) (0) (23400000000) (9),
  mkPiece 5 18 11 36 (29) (-36) (23400000000) (9),
  mkPiece 11 36 5 16 (2) (0) (2600000000) (1),
  mkPiece 5 16 25 72 (5) (16) (13000000000) (5),
  mkPiece 25 72 10 27 (19) (0) (23400000000) (9),
  mkPiece 10 27 11 27 (29) (-27) (23400000000) (9),
  mkPiece 11 27 5 11 (2) (0) (2600000000) (1),
  mkPiece 5 11 50 99 (5) (11) (13000000000) (5),
  mkPiece 50 99 5 9 (19) (0) (23400000000) (9),
  mkPiece 5 9 11 18 (29) (-18) (23400000000) (9),
  mkPiece 11 18 5 6 (2) (0) (2600000000) (1),
  mkPiece 5 6 25 27 (5) (6) (13000000000) (5),
  mkPiece 25 27 1 1 (65) (-36) (39000000000) (15),
  mkPiece 1 1 55 54 (100) (-9) (117000000000) (45),
  mkPiece 55 54 10 9 (35) (-6) (39000000000) (15),
  mkPiece 10 9 11 9 (155) (-63) (117000000000) (45),
  mkPiece 11 9 5 1 (100) (-18) (117000000000) (45),
  mkPiece 5 1 55 9 (55) (-9) (117000000000) (45),
  mkPiece 55 9 63 10 (0) (0) (2600000000) (1)]

def profile1Mass : ℚ := (351448141124711 / 58023496571040)
theorem profile1_chain : Chain (1 / 9) profile1 := by
  norm_num [profile1, Chain, mkPiece]
theorem profile1_end : lastEnd (1 / 9) profile1 = (63 / 10) := by
  norm_num [profile1, lastEnd, mkPiece]
theorem profile1_mass : listInt profile1 = (profile1Mass : ℝ) := by
  norm_num [profile1, listInt, Piece.int, profile1Mass, mkPiece]
#print axioms profile1_chain
#print axioms profile1_end
#print axioms profile1_mass
end CatalanCore.Uniform.Bank.FifthsContent
