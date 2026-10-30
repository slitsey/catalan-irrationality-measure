import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix1 : List Piece := [
  mkPiece 2 1503 1 747 (19) (747) (23400000000) (9),
  mkPiece 1 747 2 1485 (7) (-249) (7800000000) (3),
  mkPiece 2 1485 1 738 (19) (738) (23400000000) (9),
  mkPiece 1 738 2 1467 (7) (-246) (7800000000) (3),
  mkPiece 2 1467 1 729 (19) (729) (23400000000) (9),
  mkPiece 1 729 2 1449 (7) (-243) (7800000000) (3),
  mkPiece 2 1449 1 720 (19) (720) (23400000000) (9),
  mkPiece 1 720 2 1431 (7) (-240) (7800000000) (3),
  mkPiece 2 1431 1 711 (19) (711) (23400000000) (9),
  mkPiece 1 711 2 1413 (7) (-237) (7800000000) (3),
  mkPiece 2 1413 1 702 (19) (702) (23400000000) (9),
  mkPiece 1 702 2 1395 (7) (-234) (7800000000) (3),
  mkPiece 2 1395 1 693 (19) (693) (23400000000) (9),
  mkPiece 1 693 2 1377 (7) (-231) (7800000000) (3),
  mkPiece 2 1377 1 684 (19) (684) (23400000000) (9),
  mkPiece 1 684 2 1359 (7) (-228) (7800000000) (3),
  mkPiece 2 1359 1 675 (19) (675) (23400000000) (9),
  mkPiece 1 675 2 1341 (7) (-225) (7800000000) (3),
  mkPiece 2 1341 1 666 (19) (666) (23400000000) (9),
  mkPiece 1 666 2 1323 (7) (-222) (7800000000) (3),
  mkPiece 2 1323 1 657 (19) (657) (23400000000) (9),
  mkPiece 1 657 2 1305 (7) (-219) (7800000000) (3),
  mkPiece 2 1305 1 648 (19) (648) (23400000000) (9),
  mkPiece 1 648 2 1287 (7) (-216) (7800000000) (3),
  mkPiece 2 1287 1 639 (19) (639) (23400000000) (9),
  mkPiece 1 639 2 1269 (7) (-213) (7800000000) (3),
  mkPiece 2 1269 1 630 (19) (630) (23400000000) (9),
  mkPiece 1 630 2 1251 (7) (-210) (7800000000) (3),
  mkPiece 2 1251 1 621 (19) (621) (23400000000) (9),
  mkPiece 1 621 2 1233 (7) (-207) (7800000000) (3),
  mkPiece 2 1233 1 612 (19) (612) (23400000000) (9),
  mkPiece 1 612 2 1215 (7) (-204) (7800000000) (3),
  mkPiece 2 1215 1 603 (19) (603) (23400000000) (9)]

def prefix1Mass : ℚ := (235280593788673784963742411757238463720801774457 / 323140566803156811700167326253484420880766961635600)
theorem prefix1_chain : Chain (2 / 1503) prefix1 := by
  norm_num [prefix1, Chain, mkPiece]
theorem prefix1_end : lastEnd (2 / 1503) prefix1 = (1 / 603) := by
  norm_num [prefix1, lastEnd, mkPiece]
theorem prefix1_mass : listInt prefix1 = (prefix1Mass : ℝ) := by
  norm_num [prefix1, listInt, Piece.int, prefix1Mass, mkPiece]
#print axioms prefix1_chain
#print axioms prefix1_end
#print axioms prefix1_mass
end CatalanCore.Uniform.Bank.FifthsContent
