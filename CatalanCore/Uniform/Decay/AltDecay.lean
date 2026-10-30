module

public import CatalanCore.Uniform.Decay.PolyWire3.Top
public import CatalanCore.Uniform.Decay.Nodes.EnergyCheck
public import CatalanCore.Uniform.Decay.ContourCheck
public import CatalanCore.Uniform.Content.Shape.Alt

@[expose] public section
set_option Elab.async false

/-!
# Decay of any alternating bank from its tables (lane D2)

Every geometry and frame hypothesis of `PolyWire3.hasScaledDecay_of_tables3` for `altGeom c` is
discharged here once:

- the node pieces `[(1, 0, 1), (1/2, 1, 1 + c)]` (rows and columns alike);
- the total mass `1 + c / 2`;
- the supports and the block bounds;
- the node energy, by `energyCheck`;
- the contour separation, by `contourCheck`.

A bank then supplies only its tables `T`, spline datum `D` and polygon `P`, with three Boolean checks
(`T.check D P`, `energyCheck`, `contourCheck`) and the frame's floor condition `hAR`, which is
decidable.
-/

namespace CatalanCore.Uniform.Decay.AltDecay
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Decay.Nodes
  CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3 CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon

/-- The node pieces of `altGeom c`, rows and columns alike. -/
def altPieces (c : ℚ) : List (ℚ × ℚ × ℚ) := [(1, 0, 1), (1 / 2, 1, 1 + c)]

theorem altGeom_rowPieces (c : ℚ) (hc : 0 < c) :
    (altGeom c hc).rowPieces = (altPieces c).map ratPiece := by
  simp [altGeom, BlockGeom.rowPieces, BlockCollection.pieces, single, commonB, rowB,
    PeriodicBlock.piece, ratPiece, List.finRange, altPieces]

theorem altGeom_colPieces (c : ℚ) (hc : 0 < c) :
    (altGeom c hc).colPieces = (altPieces c).map ratPiece := by
  simp [altGeom, BlockGeom.colPieces, BlockCollection.pieces, single, commonB, colB,
    PeriodicBlock.piece, ratPiece, List.finRange, altPieces]

theorem altGeom_totalMass (c : ℚ) (hc : 0 < c) : (altGeom c hc).totalMass = 1 + c / 2 := by
  simp [altGeom, BlockGeom.totalMass, BlockGeom.gamma, BlockGeom.beta, single_mass, commonB, rowB,
    PeriodicBlock.mass]

theorem altGeom_supp (c : ℚ) (hc : 0 < c) :
    ∀ r a : ℕ, a ∈ ((altGeom c hc).geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  rw [altGeom_C, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem altGeom_blocks_v (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∀ i, (((altGeom c hc).common.block i).v : ℝ) ≤ 2) ∧
      (∀ i, (((altGeom c hc).row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, (((altGeom c hc).column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [altGeom, single, commonB, rowB, colB]
    try norm_num
    try (have : (c : ℝ) ≤ 1 := by exact_mod_cast hc1
         linarith)

/-- **Decay of an alternating bank from its tables.** -/
theorem altGeom_hasScaledDecay (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {Fr : Frame}
    (hC : Frame.contourCheck Fr = true)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (T : PolyTables3)
    (hRP : T.RP = altPieces c) (hCP : T.CP = altPieces c) (hMq : T.Mq = 1 + c / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = Fr.d)
    (N : ℕ) (hE : energyCheck N (altPieces c) (altPieces c) D.Inu = true)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i) (hε : 0 < D.ε) (depth : ℕ) :
    HasScaledDecay ((altGeom c hc).family Fr depth) (altGeom c hc).scale (D.Dt : ℝ)
      (D.ccert : ℝ) := by
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v c hc hc1
  have hε' : (0 : ℝ) < (D.ε : ℝ) := by exact_mod_cast hε
  exact hasScaledDecay_of_tables3 (altGeom c hc) (Frame.contourOK_of_check hC) hAR hnorm1 T
    (by rw [altGeom_rowPieces, hRP]) (by rw [altGeom_colPieces, hCP])
    (by rw [hMq, altGeom_totalMass]) D P hT hd
    (inu_le_nodeEnergy_of_check (altGeom_rowPieces c hc) (altGeom_colPieces c hc) hE)
    (altGeom_supp c hc) (Bd := 2) (by norm_num) hbc hbr hbq hm0 hm0μ
    (e := (D.ε : ℝ) / 2) (by linarith) (by linarith) depth

end CatalanCore.Uniform.Decay.AltDecay
