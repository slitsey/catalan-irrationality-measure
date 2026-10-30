import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix0 : List Piece := [
  mkPiece 1 900 2 1791 (7) (-300) (7800000000) (3),
  mkPiece 2 1791 1 891 (19) (891) (23400000000) (9),
  mkPiece 1 891 2 1773 (7) (-297) (7800000000) (3),
  mkPiece 2 1773 1 882 (19) (882) (23400000000) (9),
  mkPiece 1 882 2 1755 (7) (-294) (7800000000) (3),
  mkPiece 2 1755 1 873 (19) (873) (23400000000) (9),
  mkPiece 1 873 2 1737 (7) (-291) (7800000000) (3),
  mkPiece 2 1737 1 864 (19) (864) (23400000000) (9),
  mkPiece 1 864 2 1719 (7) (-288) (7800000000) (3),
  mkPiece 2 1719 1 855 (19) (855) (23400000000) (9),
  mkPiece 1 855 2 1701 (7) (-285) (7800000000) (3),
  mkPiece 2 1701 1 846 (19) (846) (23400000000) (9),
  mkPiece 1 846 2 1683 (7) (-282) (7800000000) (3),
  mkPiece 2 1683 1 837 (19) (837) (23400000000) (9),
  mkPiece 1 837 2 1665 (7) (-279) (7800000000) (3),
  mkPiece 2 1665 1 828 (19) (828) (23400000000) (9),
  mkPiece 1 828 2 1647 (7) (-276) (7800000000) (3),
  mkPiece 2 1647 1 819 (19) (819) (23400000000) (9),
  mkPiece 1 819 2 1629 (7) (-273) (7800000000) (3),
  mkPiece 2 1629 1 810 (19) (810) (23400000000) (9),
  mkPiece 1 810 2 1611 (7) (-270) (7800000000) (3),
  mkPiece 2 1611 1 801 (19) (801) (23400000000) (9),
  mkPiece 1 801 2 1593 (7) (-267) (7800000000) (3),
  mkPiece 2 1593 1 792 (19) (792) (23400000000) (9),
  mkPiece 1 792 2 1575 (7) (-264) (7800000000) (3),
  mkPiece 2 1575 1 783 (19) (783) (23400000000) (9),
  mkPiece 1 783 2 1557 (7) (-261) (7800000000) (3),
  mkPiece 2 1557 1 774 (19) (774) (23400000000) (9),
  mkPiece 1 774 2 1539 (7) (-258) (7800000000) (3),
  mkPiece 2 1539 1 765 (19) (765) (23400000000) (9),
  mkPiece 1 765 2 1521 (7) (-255) (7800000000) (3),
  mkPiece 2 1521 1 756 (19) (756) (23400000000) (9),
  mkPiece 1 756 2 1503 (7) (-252) (7800000000) (3)]

def prefix0Mass : ℚ := (272533146818135227535097056130451568822012445083 / 558645809194878577563815380869128490215069665336800)
theorem prefix0_chain : Chain (1 / 900) prefix0 := by
  norm_num [prefix0, Chain, mkPiece]
theorem prefix0_end : lastEnd (1 / 900) prefix0 = (2 / 1503) := by
  norm_num [prefix0, lastEnd, mkPiece]
theorem prefix0_mass : listInt prefix0 = (prefix0Mass : ℝ) := by
  norm_num [prefix0, listInt, Piece.int, prefix0Mass, mkPiece]
#print axioms prefix0_chain
#print axioms prefix0_end
#print axioms prefix0_mass
end CatalanCore.Uniform.Bank.FifthsContent
