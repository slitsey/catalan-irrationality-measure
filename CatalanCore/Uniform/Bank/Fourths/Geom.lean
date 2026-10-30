module

public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Decay.Nodes.Limit
public import CatalanCore.Uniform.Decay.PolyFull.CapNodes

@[expose] public section
set_option Elab.async false



namespace CatalanCore.Uniform.Bank.Fourths
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem one_fifth_pos : (0 : ℚ) < 1 / 5 := by norm_num


noncomputable def FL : BlockGeom := altGeom (1 / 5) one_fifth_pos

theorem FL_rowPieces :
    FL.rowPieces = [(1, 0, 1), (1 / 2, 1, 6 / 5)].map ratPiece := by
  simp [FL, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem FL_colPieces :
    FL.colPieces = [(1, 0, 1), (1 / 2, 1, 6 / 5)].map ratPiece := by
  simp [FL, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem FL_totalMass : FL.totalMass = 11 / 10 := by
  simp [FL, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

theorem FL_common_mass : FL.common.mass = 1 := by
  simp [FL, altGeom, single_mass, commonB, PeriodicBlock.mass]

theorem FL_hyb {r : ℕ} (hr : r % 2 = 0) : HybShape FL r := altGeom_hybShape _ one_fifth_pos hr

theorem FL_supp : ∀ r a : ℕ, a ∈ (FL.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (FL.geometry r).C = Finset.range r := altGeom_C _ one_fifth_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem FL_blocks_v :
    (∀ i, ((FL.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((FL.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((FL.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [FL, altGeom, single, commonB, rowB, colB]
    try norm_num

end CatalanCore.Uniform.Bank.Fourths
