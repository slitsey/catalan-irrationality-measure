module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/Trimmed130Geometry.lean
Original SHA256: bc0582026b69003fe2cdeb9b66fe2bd18ce357a84f2a02e255fc54a7625a5260
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.Trimmed130BranchData
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130ZeroData
public import CatalanMeasure.GenD.Signed.Davis.PolynomialData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem branch_ordered : ∀ i : Fin 130, branchLeft i < branchRight i := by decide +kernel

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem branch_adjacent : ∀ i : Fin 129, branchRight i.castSucc ≤ branchLeft i.succ := by
  decide +kernel

theorem branch_separated : ∀ i j : Fin 130, i < j → branchRight i ≤ branchLeft j :=
  ordered_intervals_separated (fun i => (branch_ordered i).le) branch_adjacent

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem branch_geometry : ∀ i : Fin 130,
    -1 ≤ branchLeft i ∧ branchRight i ≤ 1 ∧
      ((outerLeft ≤ branchLeft i ∧ branchRight i ≤ innerLeft) ∨
        (innerRight ≤ branchLeft i ∧ branchRight i ≤ 1)) := by decide +kernel

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem zero_ordered : ∀ i : Fin 130, zeroLeft i < zeroRight i := by decide +kernel

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem zero_geometry : ∀ i : Fin 130, -1 ≤ zeroLeft i ∧ zeroRight i ≤ 1 := by
  decide +kernel

-- kcost: 5 s estimated per inherited finite check; at most 131 coefficient/list entries or 130 branch intervals. No generated bulk certificate is added; inspect first measured module before scaling.
theorem zero_adjacent : ∀ i : Fin 129, zeroRight i.castSucc ≤ zeroLeft i.succ := by
  decide +kernel

theorem zero_separated : ∀ i j : Fin 130, i < j → zeroRight i ≤ zeroLeft j :=
  ordered_intervals_separated (fun i => (zero_ordered i).le) zero_adjacent

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.branch_ordered
#print axioms CatalanMeasure.Refinement.Trimmed130.branch_adjacent
#print axioms CatalanMeasure.Refinement.Trimmed130.branch_separated
#print axioms CatalanMeasure.Refinement.Trimmed130.branch_geometry
#print axioms CatalanMeasure.Refinement.Trimmed130.zero_ordered
#print axioms CatalanMeasure.Refinement.Trimmed130.zero_geometry
#print axioms CatalanMeasure.Refinement.Trimmed130.zero_adjacent
#print axioms CatalanMeasure.Refinement.Trimmed130.zero_separated
