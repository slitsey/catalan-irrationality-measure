import CatalanCore.Uniform.Content.Shape.Alt
import CatalanCore.Uniform.Decay.Nodes.Limit
import CatalanCore.Uniform.Decay.PolyFull.CapNodes
import CatalanLambda.Cert.LogBounds
set_option Elab.async false

/-! The chi3 node geometry `altGeom (1/2)` (lane B, B3f): limiting pieces, total mass, node energy. -/

namespace CatalanCore.Uniform.Bank.Chi3New
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem half_pos : (0 : ℚ) < 1 / 2 := by norm_num

/-- The block geometry of the chi3 bank: common `[0, r)`, row = even and column = odd integers
in `[r, 3r/2)`. -/
noncomputable def G12 : BlockGeom := altGeom (1 / 2) half_pos

theorem G12_rowPieces :
    G12.rowPieces = [(1, 0, 1), (1 / 2, 1, 3 / 2)].map ratPiece := by
  simp [G12, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem G12_colPieces :
    G12.colPieces = [(1, 0, 1), (1 / 2, 1, 3 / 2)].map ratPiece := by
  simp [G12, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem G12_totalMass : G12.totalMass = 5 / 4 := by
  simp [G12, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

end CatalanCore.Uniform.Bank.Chi3New
