import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix2 : List Piece := [
  mkPiece 1 603 2 1197 (7) (-201) (7800000000) (3),
  mkPiece 2 1197 1 594 (19) (594) (23400000000) (9),
  mkPiece 1 594 2 1179 (7) (-198) (7800000000) (3),
  mkPiece 2 1179 1 585 (19) (585) (23400000000) (9),
  mkPiece 1 585 2 1161 (7) (-195) (7800000000) (3),
  mkPiece 2 1161 1 576 (19) (576) (23400000000) (9),
  mkPiece 1 576 2 1143 (7) (-192) (7800000000) (3),
  mkPiece 2 1143 1 567 (19) (567) (23400000000) (9),
  mkPiece 1 567 2 1125 (7) (-189) (7800000000) (3),
  mkPiece 2 1125 1 558 (19) (558) (23400000000) (9),
  mkPiece 1 558 2 1107 (7) (-186) (7800000000) (3),
  mkPiece 2 1107 1 549 (19) (549) (23400000000) (9),
  mkPiece 1 549 2 1089 (7) (-183) (7800000000) (3),
  mkPiece 2 1089 1 540 (19) (540) (23400000000) (9),
  mkPiece 1 540 2 1071 (7) (-180) (7800000000) (3),
  mkPiece 2 1071 1 531 (19) (531) (23400000000) (9),
  mkPiece 1 531 2 1053 (7) (-177) (7800000000) (3),
  mkPiece 2 1053 1 522 (19) (522) (23400000000) (9),
  mkPiece 1 522 2 1035 (7) (-174) (7800000000) (3),
  mkPiece 2 1035 1 513 (19) (513) (23400000000) (9),
  mkPiece 1 513 2 1017 (7) (-171) (7800000000) (3),
  mkPiece 2 1017 1 504 (19) (504) (23400000000) (9),
  mkPiece 1 504 2 999 (7) (-168) (7800000000) (3),
  mkPiece 2 999 1 495 (19) (495) (23400000000) (9),
  mkPiece 1 495 2 981 (7) (-165) (7800000000) (3),
  mkPiece 2 981 1 486 (19) (486) (23400000000) (9),
  mkPiece 1 486 2 963 (7) (-162) (7800000000) (3),
  mkPiece 2 963 1 477 (19) (477) (23400000000) (9),
  mkPiece 1 477 2 945 (7) (-159) (7800000000) (3),
  mkPiece 2 945 1 468 (19) (468) (23400000000) (9),
  mkPiece 1 468 2 927 (7) (-156) (7800000000) (3),
  mkPiece 2 927 1 459 (19) (459) (23400000000) (9),
  mkPiece 1 459 2 909 (7) (-153) (7800000000) (3)]

def prefix2Mass : ℚ := (29747762122259430093504117803409094332519631 / 24710745397848699587190441427492005564568296000)
theorem prefix2_chain : Chain (1 / 603) prefix2 := by
  norm_num [prefix2, Chain, mkPiece]
theorem prefix2_end : lastEnd (1 / 603) prefix2 = (2 / 909) := by
  norm_num [prefix2, lastEnd, mkPiece]
theorem prefix2_mass : listInt prefix2 = (prefix2Mass : ℝ) := by
  norm_num [prefix2, listInt, Piece.int, prefix2Mass, mkPiece]
#print axioms prefix2_chain
#print axioms prefix2_end
#print axioms prefix2_mass
end CatalanCore.Uniform.Bank.FifthsContent
