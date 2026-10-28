module
public import CatalanCore.Uniform.Decay.Nodes.Pieces
@[expose] public section

/-!
# Limiting node measures of a `BlockGeom`, and the separate row/column energies

`μ_R = μ_C + μ_X`, `μ_Q = μ_C + μ_Y` are lists of pieces (`1/d` on `[u, v]` per block residue);
`gamma = μ_C(ℝ)`, `beta = μ_X(ℝ) = μ_Y(ℝ)`, `M = gamma + beta`; the node energy is
`J_node = (I(μ_R) + I(μ_Q))/2` and is NOT `I(ν)` (explicit gap `log 2` in an example).
-/

namespace CatalanCore.Uniform
open Decay.Nodes

namespace PeriodicBlock

/-- The limiting measure of one block residue: density `1/d` on `[u, v]`. -/
noncomputable def piece (b : PeriodicBlock) : Piece :=
  ⟨1 / (b.d : ℝ), (b.u : ℝ), (b.v : ℝ)⟩

theorem piece_mass (b : PeriodicBlock) : b.piece.mass = (b.mass : ℝ) := by
  unfold piece Piece.mass mass
  push_cast
  ring

/-- **Prefix prediction = limiting CDF.** `prefixMass r x = r · cdf (x/r)`. -/
theorem prefixMass_eq_cdf (b : PeriodicBlock) {r : ℕ} (hr : 0 < r) (x : ℚ) :
    ((b.prefixMass r x : ℚ) : ℝ) = r * b.piece.cdf ((x : ℝ) / r) := by
  have hd : (0 : ℝ) < b.d := by exact_mod_cast b.hd
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold prefixMass Piece.cdf piece mass
  push_cast
  have hc : (0 : ℝ) ≤ r / b.d := by positivity
  have e1 : ((x : ℝ) - b.u * r) / b.d = (r / b.d) * ((x : ℝ) / r - b.u) := by
    field_simp
  have e2 : ((b.v : ℝ) - b.u) / b.d * r = (r / b.d) * ((b.v : ℝ) - b.u) := by ring
  have e3 : (r : ℝ) * (1 / b.d * max 0 (min ((x : ℝ) / r) b.v - b.u)) =
      (r / b.d) * max 0 (min ((x : ℝ) / r) b.v - b.u) := by ring
  rw [e1, e2, ← mul_min_of_nonneg _ _ hc, min_sub_sub_right, e3, mul_max_of_nonneg _ _ hc,
    mul_zero]

end PeriodicBlock

namespace BlockCollection

/-- Limiting measure of a block collection. -/
noncomputable def pieces (B : BlockCollection) : List Piece :=
  (List.finRange B.n).map fun i => (B.block i).piece

theorem pieces_mass (B : BlockCollection) : pmass B.pieces = (B.mass : ℝ) := by
  unfold pmass pieces mass
  rw [List.map_map, ← Fin.sum_univ_def]
  push_cast
  exact Finset.sum_congr rfl fun i _ => (B.block i).piece_mass

end BlockCollection

namespace BlockGeom

/-- Row limiting measure `μ_R = μ_C + μ_X`. -/
noncomputable def rowPieces (G : BlockGeom) : List Piece := G.common.pieces ++ G.row.pieces

/-- Column limiting measure `μ_Q = μ_C + μ_Y`. -/
noncomputable def colPieces (G : BlockGeom) : List Piece := G.common.pieces ++ G.column.pieces

theorem pmass_append (A B : List Piece) : pmass (A ++ B) = pmass A + pmass B := by
  simp [pmass]

/-- Common degree mass `gamma`. -/
def gamma (G : BlockGeom) : ℚ := G.common.mass

/-- Border mass `beta`. -/
def beta (G : BlockGeom) : ℚ := G.row.mass

/-- Total source mass `M = gamma + beta`. -/
def totalMass (G : BlockGeom) : ℚ := G.gamma + G.beta

theorem pmass_rowPieces (G : BlockGeom) : pmass G.rowPieces = (G.totalMass : ℝ) := by
  unfold rowPieces totalMass gamma beta
  rw [pmass_append, G.common.pieces_mass, G.row.pieces_mass]
  push_cast; ring

/-- Row and column measures have the same mass `M` (balanced borders). -/
theorem pmass_colPieces (G : BlockGeom) : pmass G.colPieces = (G.totalMass : ℝ) := by
  unfold colPieces totalMass gamma beta
  rw [pmass_append, G.common.pieces_mass, G.column.pieces_mass, ← G.border_mass]
  push_cast; ring

/-- The node energy `J_node`, the average of the two separate energies. -/
noncomputable def nodeEnergy (G : BlockGeom) : ℝ :=
  Decay.Nodes.nodeEnergy G.rowPieces G.colPieces

end BlockGeom

end CatalanCore.Uniform

namespace CatalanCore.Uniform.Decay.Nodes

theorem Hfun_zero : Hfun 0 = 0 := by simp [Hfun]

theorem Hfun_one : Hfun 1 = -3 / 4 := by simp [Hfun]; norm_num

theorem Hfun_negone : Hfun (-1) = -3 / 4 := by rw [Hfun_neg, Hfun_one]

theorem Hfun_two : Hfun 2 = 2 * Real.log 2 - 3 := by unfold Hfun; norm_num; ring

theorem Hfun_negtwo : Hfun (-2) = 2 * Real.log 2 - 3 := by rw [Hfun_neg, Hfun_two]

/-- An explicit adversary: row `Leb[0,1]`, column `Leb[1,2]`.  `I(μR) = I(μQ) = 3/2`,
`I(μR,μQ) = 3/2 - 2 log 2`; hence the averaged-measure energy is `3/2 - log 2`, while the node
energy is `3/2`.  The two differ by exactly `log 2`. -/
theorem nodeEnergy_gap_example :
    nodeEnergy [⟨1, 0, 1⟩] [⟨1, 1, 2⟩] -
      selfEnergy (avgMeasure [⟨1, 0, 1⟩] [⟨1, 1, 2⟩]) = Real.log 2 := by
  rw [nodeEnergy_eq_avg_add]
  have hRR : selfEnergy [⟨1, 0, 1⟩] = 3 / 2 := by
    simp only [selfEnergy, mutE, pairInteraction, pairEnergy, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    norm_num [Hfun_zero, Hfun_one, Hfun_negone]
  have hQQ : selfEnergy [⟨1, 1, 2⟩] = 3 / 2 := by
    simp only [selfEnergy, mutE, pairInteraction, pairEnergy, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    norm_num [Hfun_zero, Hfun_one, Hfun_negone]
  have hRQ : mutE [⟨1, 0, 1⟩] [⟨1, 1, 2⟩] = 3 / 2 - 2 * Real.log 2 := by
    simp only [mutE, pairInteraction, pairEnergy, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    norm_num [Hfun_zero, Hfun_one, Hfun_negone, Hfun_two, Hfun_negtwo]
    ring
  rw [hRR, hQQ, hRQ]
  ring

end CatalanCore.Uniform.Decay.Nodes
