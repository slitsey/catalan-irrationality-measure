import CatalanCore.Uniform.Content.Shape.Alt
import CatalanCore.Uniform.Decay.Nodes.Limit
import CatalanCore.Uniform.Decay.PolyFull.CapNodes
set_option Elab.async false

/-! The sevenths node geometry `altGeom (2/9)` (lane B, B5): limiting pieces, total mass, support. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem one_sixth_pos : (0 : ℚ) < 1 / 6 := by norm_num

/-- Alternating common-deletion geometry with border slope `1/12`. -/
noncomputable def F7 : BlockGeom := altGeom (1 / 6) one_sixth_pos

theorem F7_rowPieces :
    F7.rowPieces = [(1, 0, 1), (1 / 2, 1, 7 / 6)].map ratPiece := by
  simp [F7, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem F7_colPieces :
    F7.colPieces = [(1, 0, 1), (1 / 2, 1, 7 / 6)].map ratPiece := by
  simp [F7, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem F7_totalMass : F7.totalMass = 13 / 12 := by
  simp [F7, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

theorem F7_common_mass : F7.common.mass = 1 := by
  simp [F7, altGeom, single_mass, commonB, PeriodicBlock.mass]

theorem F7_hyb {r : ℕ} (hr : r % 2 = 0) : HybShape F7 r := altGeom_hybShape _ one_sixth_pos hr

theorem F7_supp : ∀ r a : ℕ, a ∈ (F7.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (F7.geometry r).C = Finset.range r := altGeom_C _ one_sixth_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem F7_blocks_v :
    (∀ i, ((F7.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((F7.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((F7.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [F7, altGeom, single, commonB, rowB, colB]
    try norm_num

end CatalanCore.Uniform.Bank.Sevenths
