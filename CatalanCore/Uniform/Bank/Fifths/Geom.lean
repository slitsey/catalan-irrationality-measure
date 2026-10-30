module

public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Decay.Nodes.Limit
public import CatalanCore.Uniform.Decay.PolyFull.CapNodes

@[expose] public section
set_option Elab.async false

/-! The fifths node geometry `altGeom (2/9)` (lane B, B5): limiting pieces, total mass, support. -/

namespace CatalanCore.Uniform.Bank.Fifths
open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull

theorem two_ninths_pos : (0 : ℚ) < 2 / 9 := by norm_num

/-- The block geometry of the fifths bank: common `[0, r)`, rows = even and columns = odd integers
in `[r, 11 r / 9)`, so `m ≈ r / 9` border pairs. -/
noncomputable def F5 : BlockGeom := altGeom (2 / 9) two_ninths_pos

theorem F5_rowPieces :
    F5.rowPieces = [(1, 0, 1), (1 / 2, 1, 11 / 9)].map ratPiece := by
  simp [F5, altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem F5_colPieces :
    F5.colPieces = [(1, 0, 1), (1 / 2, 1, 11 / 9)].map ratPiece := by
  simp [F5, altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange]
  norm_num

theorem F5_totalMass : F5.totalMass = 10 / 9 := by
  simp [F5, altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass,
    commonB, rowB, PeriodicBlock.mass]
  norm_num

theorem F5_common_mass : F5.common.mass = 1 := by
  simp [F5, altGeom, single_mass, commonB, PeriodicBlock.mass]

theorem F5_hyb {r : ℕ} (hr : r % 2 = 0) : HybShape F5 r := altGeom_hybShape _ two_ninths_pos hr

theorem F5_supp : ∀ r a : ℕ, a ∈ (F5.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (F5.geometry r).C = Finset.range r := altGeom_C _ two_ninths_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem F5_blocks_v :
    (∀ i, ((F5.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((F5.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((F5.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [F5, altGeom, single, commonB, rowB, colB]
    try norm_num

end CatalanCore.Uniform.Bank.Fifths
