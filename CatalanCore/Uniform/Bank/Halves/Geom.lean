import CatalanCore.Uniform.Content.Shape.Alt
import CatalanCore.Uniform.Decay.Nodes.Limit
import CatalanCore.Uniform.Decay.PolyFull.CapNodes
set_option Elab.async false

/-! The halves node geometry `altGeom (3/10)` : limiting pieces, total mass, support. -/

namespace CatalanCore.Uniform.Bank.Halves
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem three_tenths_pos : (0 : ℚ) < 3 / 10 := by norm_num

/-- The block geometry of the halves bank: common `[0, r)`, rows = even and columns = odd integers
in `[r, 13 r / 10)`, so `m ≈ 3 r / 20` border pairs. -/
noncomputable def FH : BlockGeom := altGeom (3 / 10) three_tenths_pos

theorem FH_rowPieces :
    FH.rowPieces = [(1, 0, 1), (1 / 2, 1, 13 / 10)].map ratPiece := by
  simp [FH, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem FH_colPieces :
    FH.colPieces = [(1, 0, 1), (1 / 2, 1, 13 / 10)].map ratPiece := by
  simp [FH, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem FH_totalMass : FH.totalMass = 23 / 20 := by
  simp [FH, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

theorem FH_common_mass : FH.common.mass = 1 := by
  simp [FH, altGeom, single_mass, commonB, PeriodicBlock.mass]

theorem FH_hyb {r : ℕ} (hr : r % 2 = 0) : HybShape FH r := altGeom_hybShape _ three_tenths_pos hr

theorem FH_supp : ∀ r a : ℕ, a ∈ (FH.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (FH.geometry r).C = Finset.range r := altGeom_C _ three_tenths_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem FH_blocks_v :
    (∀ i, ((FH.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((FH.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((FH.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [FH, altGeom, single, commonB, rowB, colB]
    try norm_num

end CatalanCore.Uniform.Bank.Halves
