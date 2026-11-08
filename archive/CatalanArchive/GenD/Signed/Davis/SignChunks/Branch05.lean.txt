module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/SignChunks/Branch05.lean
Original SHA256: 4cf6a4eae0dfe719da7099e70a822677c39a15a723371879c2ab3fbf41fdd499
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.Trimmed130SignData

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CatalanMeasure.Refinement.Trimmed130

-- kcost: 10 s estimated; ten branch signs, at most 40 degree-130 homogeneous Horner evaluations (5240 stages), plus sign comparisons. One inherited ten-value chunk; measure Branch00 before further sign submissions.
theorem branch_sign_chunk_5 : ∀ j : Fin 10,
    branchScaledSign (signIndex ⟨5, by decide⟩ j) := by decide +kernel

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.branch_sign_chunk_5
