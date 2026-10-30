import CatalanCore.Uniform.Content.Member.Template
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore.Arith.Hybrid
noncomputable def prefix4 : List Piece := [
  mkPiece 1 306 2 603 (7) (-102) (7800000000) (3),
  mkPiece 2 603 1 297 (19) (297) (23400000000) (9),
  mkPiece 1 297 2 585 (7) (-99) (7800000000) (3),
  mkPiece 2 585 1 288 (19) (288) (23400000000) (9),
  mkPiece 1 288 2 567 (7) (-96) (7800000000) (3),
  mkPiece 2 567 1 279 (19) (279) (23400000000) (9),
  mkPiece 1 279 2 549 (7) (-93) (7800000000) (3),
  mkPiece 2 549 1 270 (19) (270) (23400000000) (9),
  mkPiece 1 270 2 531 (7) (-90) (7800000000) (3),
  mkPiece 2 531 1 261 (19) (261) (23400000000) (9),
  mkPiece 1 261 2 513 (7) (-87) (7800000000) (3),
  mkPiece 2 513 1 252 (19) (252) (23400000000) (9),
  mkPiece 1 252 2 495 (7) (-84) (7800000000) (3),
  mkPiece 2 495 1 243 (19) (243) (23400000000) (9),
  mkPiece 1 243 2 477 (7) (-81) (7800000000) (3),
  mkPiece 2 477 1 234 (19) (234) (23400000000) (9),
  mkPiece 1 234 2 459 (7) (-78) (7800000000) (3),
  mkPiece 2 459 1 225 (19) (225) (23400000000) (9),
  mkPiece 1 225 2 441 (7) (-75) (7800000000) (3),
  mkPiece 2 441 1 216 (19) (216) (23400000000) (9),
  mkPiece 1 216 2 423 (7) (-72) (7800000000) (3),
  mkPiece 2 423 1 207 (19) (207) (23400000000) (9),
  mkPiece 1 207 2 405 (7) (-69) (7800000000) (3),
  mkPiece 2 405 1 198 (19) (198) (23400000000) (9),
  mkPiece 1 198 2 387 (7) (-66) (7800000000) (3),
  mkPiece 2 387 1 189 (19) (189) (23400000000) (9),
  mkPiece 1 189 2 369 (7) (-63) (7800000000) (3),
  mkPiece 2 369 1 180 (19) (180) (23400000000) (9),
  mkPiece 1 180 2 351 (7) (-60) (7800000000) (3),
  mkPiece 2 351 1 171 (19) (171) (23400000000) (9),
  mkPiece 1 171 2 333 (7) (-57) (7800000000) (3),
  mkPiece 2 333 1 162 (19) (162) (23400000000) (9),
  mkPiece 1 162 2 315 (7) (-54) (7800000000) (3)]

def prefix4Mass : ℚ := (627269426147416762380724619 / 91659462571800234939773705760)
theorem prefix4_chain : Chain (1 / 306) prefix4 := by
  norm_num [prefix4, Chain, mkPiece]
theorem prefix4_end : lastEnd (1 / 306) prefix4 = (2 / 315) := by
  norm_num [prefix4, lastEnd, mkPiece]
theorem prefix4_mass : listInt prefix4 = (prefix4Mass : ℝ) := by
  norm_num [prefix4, listInt, Piece.int, prefix4Mass, mkPiece]
#print axioms prefix4_chain
#print axioms prefix4_end
#print axioms prefix4_mass
end CatalanCore.Uniform.Bank.FifthsContent
