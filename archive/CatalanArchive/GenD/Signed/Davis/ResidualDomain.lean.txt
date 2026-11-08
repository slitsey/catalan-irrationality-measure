module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Improvement/Fields/ResidualDomain.lean
Original SHA256: 6d8f1f53d916b690a467834b1dfad02b35c9268becd69bc0786f9607a749aae0
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import Mathlib.Data.Real.Basic

@[expose] public section

namespace CatalanMeasure.Improvement.Fields

def trimmedResidualCap : ℚ := -883 / 10000

def trimmedResidualSupport (x : ℝ) : Prop :=
  (-2409 / 2500 ≤ x ∧ x ≤ -19501 / 100000) ∨
    (98749 / 1000000 ≤ x ∧ x ≤ 1)

end CatalanMeasure.Improvement.Fields


-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Improvement.Fields.trimmedResidualCap
#print axioms CatalanMeasure.Improvement.Fields.trimmedResidualSupport
