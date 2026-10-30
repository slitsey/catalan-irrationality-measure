import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix3 : List Piece := [
  mkPiece 2 909 1 450 (19) (450) (23400000000) (9),
  mkPiece 1 450 2 891 (7) (-150) (7800000000) (3),
  mkPiece 2 891 1 441 (19) (441) (23400000000) (9),
  mkPiece 1 441 2 873 (7) (-147) (7800000000) (3),
  mkPiece 2 873 1 432 (19) (432) (23400000000) (9),
  mkPiece 1 432 2 855 (7) (-144) (7800000000) (3),
  mkPiece 2 855 1 423 (19) (423) (23400000000) (9),
  mkPiece 1 423 2 837 (7) (-141) (7800000000) (3),
  mkPiece 2 837 1 414 (19) (414) (23400000000) (9),
  mkPiece 1 414 2 819 (7) (-138) (7800000000) (3),
  mkPiece 2 819 1 405 (19) (405) (23400000000) (9),
  mkPiece 1 405 2 801 (7) (-135) (7800000000) (3),
  mkPiece 2 801 1 396 (19) (396) (23400000000) (9),
  mkPiece 1 396 2 783 (7) (-132) (7800000000) (3),
  mkPiece 2 783 1 387 (19) (387) (23400000000) (9),
  mkPiece 1 387 2 765 (7) (-129) (7800000000) (3),
  mkPiece 2 765 1 378 (19) (378) (23400000000) (9),
  mkPiece 1 378 2 747 (7) (-126) (7800000000) (3),
  mkPiece 2 747 1 369 (19) (369) (23400000000) (9),
  mkPiece 1 369 2 729 (7) (-123) (7800000000) (3),
  mkPiece 2 729 1 360 (19) (360) (23400000000) (9),
  mkPiece 1 360 2 711 (7) (-120) (7800000000) (3),
  mkPiece 2 711 1 351 (19) (351) (23400000000) (9),
  mkPiece 1 351 2 693 (7) (-117) (7800000000) (3),
  mkPiece 2 693 1 342 (19) (342) (23400000000) (9),
  mkPiece 1 342 2 675 (7) (-114) (7800000000) (3),
  mkPiece 2 675 1 333 (19) (333) (23400000000) (9),
  mkPiece 1 333 2 657 (7) (-111) (7800000000) (3),
  mkPiece 2 657 1 324 (19) (324) (23400000000) (9),
  mkPiece 1 324 2 639 (7) (-108) (7800000000) (3),
  mkPiece 2 639 1 315 (19) (315) (23400000000) (9),
  mkPiece 1 315 2 621 (7) (-105) (7800000000) (3),
  mkPiece 2 621 1 306 (19) (306) (23400000000) (9)]

def prefix3Mass : ℚ := (2673129669381998814423212661049415197 / 1126924892173380073581645895506323674800)
theorem prefix3_chain : Chain (2 / 909) prefix3 := by
  norm_num [prefix3, Chain, mkPiece]
theorem prefix3_end : lastEnd (2 / 909) prefix3 = (1 / 306) := by
  norm_num [prefix3, lastEnd, mkPiece]
theorem prefix3_mass : listInt prefix3 = (prefix3Mass : ℝ) := by
  norm_num [prefix3, listInt, Piece.int, prefix3Mass, mkPiece]
#print axioms prefix3_chain
#print axioms prefix3_end
#print axioms prefix3_mass
end CatalanCore.Uniform.Bank.FifthsContent
