module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/Trimmed130Branches.lean
Original SHA256: a4becf2fbecd365c3d1de4ed9340f6c2ee359c9c6c2b15df516870f8fa8a76ae
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.InverseBranches
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Degree
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130BranchChecks

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

open Polynomial Set CatalanMeasure.GenD.Analytic

noncomputable def branchCertificate : InverseBranchCertificate realP 130 allowedT where
  left i := (branchLeft i : ℝ)
  right i := (branchRight i : ℝ)
  ordered i := by exact_mod_cast branch_ordered i
  separated i j hij := by exact_mod_cast branch_separated i j hij
  support i x hx := by
    have hg : (-1 : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ 1 ∧
        (((outerLeft : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ innerLeft) ∨
          ((innerRight : ℝ) ≤ branchLeft i ∧ (branchRight i : ℝ) ≤ 1)) := by
      exact_mod_cast branch_geometry i
    have hleft : (innerLeft : ℝ) < 0 := by norm_num [innerLeft]
    have hright : (0 : ℝ) < innerRight := by norm_num [innerRight]
    refine ⟨⟨lt_of_le_of_lt hg.1 hx.1, lt_of_lt_of_le hx.2 hg.2.1⟩, ?_, ?_⟩
    · rcases hg.2.2 with hl | hr
      · exact ne_of_lt (lt_trans (lt_of_lt_of_le hx.2 hl.2) hleft)
      · exact ne_of_gt (lt_trans hright (lt_of_le_of_lt hr.1 hx.1))
    · rcases hg.2.2 with hl | hr
      · exact Or.inl ⟨(lt_of_le_of_lt hl.1 hx.1).le, (lt_of_lt_of_le hx.2 hl.2).le⟩
      · exact Or.inr ⟨(lt_of_le_of_lt hr.1 hx.1).le, (lt_of_lt_of_le hx.2 hr.2).le⟩
  alternating i := by
    rw [realP_eval_rational, realP_eval_rational]
    exact_mod_cast branch_signs i

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.branchCertificate
