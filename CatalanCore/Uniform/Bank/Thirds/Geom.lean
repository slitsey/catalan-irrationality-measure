import CatalanCore.Uniform.Content.Shape.Alt
import CatalanCore.Uniform.Decay.Nodes.Limit
import CatalanCore.Uniform.Decay.PolyFull.CapNodes
import CatalanLambda.Cert.LogBounds
set_option Elab.async false

/-! The thirds node geometry `altGeom (3/10)` (lane B, B4): limiting pieces, total mass, node energy.
Same statements as `Chi3New.Geom/Energy` with the slope `c = 2 * (3/20) = 3/10`. -/

namespace CatalanCore.Uniform.Bank.Thirds
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem c310_pos : (0 : ℚ) < 3 / 10 := by norm_num

/-- The block geometry of the thirds bank: common `[0, r)`, row = even and column = odd integers
in `[r, 13 r / 10)`. -/
noncomputable def G310 : BlockGeom := altGeom (3 / 10) c310_pos

theorem G310_rowPieces :
    G310.rowPieces = [(1, 0, 1), (1 / 2, 1, 13 / 10)].map ratPiece := by
  simp [G310, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem G310_colPieces :
    G310.colPieces = [(1, 0, 1), (1 / 2, 1, 13 / 10)].map ratPiece := by
  simp [G310, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem G310_totalMass : G310.totalMass = 23 / 20 := by
  simp [G310, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

theorem G310_common_mass : G310.common.mass = 1 := by
  simp [G310, altGeom, single_mass, commonB, PeriodicBlock.mass]

end CatalanCore.Uniform.Bank.Thirds
