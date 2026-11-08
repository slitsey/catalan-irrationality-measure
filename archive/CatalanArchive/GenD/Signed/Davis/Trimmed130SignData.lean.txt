module

/-
Ported from C. Davis, catalan-constant, Apache-2.0.
Source: https://github.com/1337isnot1337/catalan-constant/blob/3c4515314bda407d032cb55f60bfc56b03c1d3f9/Submission/Refinement/Trimmed130SignData.lean
Original SHA256: b0e1d85a91ff131951ce231306c9996723dcd7fb850ff55167129e45bec5edb2
Local changes: import relocation, cost/provenance comments, axiom audit commands.
See this directory's LICENSE, NOTICE and PROVENANCE.json.
-/

public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Geometry
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130IntegerData

@[expose] public section

namespace CatalanMeasure.Refinement.Trimmed130

def signIndex (b : Fin 13) (j : Fin 10) : Fin 130 :=
  ⟨10 * b.val + j.val, by have := b.isLt; have := j.isLt; omega⟩

theorem signIndex_surjective (i : Fin 130) : ∃ b j, signIndex b j = i := by
  let b : Fin 13 := ⟨i.val / 10, by have := i.isLt; omega⟩
  let j : Fin 10 := ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩
  refine ⟨b, j, Fin.ext ?_⟩
  have h := Nat.mod_add_div i.val 10
  dsimp [signIndex, b, j]
  omega

def branchScaledSign (i : Fin 130) : Prop :=
  (scaledValue (branchLeft i) < (-1) * scaledUnit (branchLeft i) ∧
    1 * scaledUnit (branchRight i) < scaledValue (branchRight i)) ∨
  (scaledValue (branchRight i) < (-1) * scaledUnit (branchRight i) ∧
    1 * scaledUnit (branchLeft i) < scaledValue (branchLeft i))

def zeroScaledSign (i : Fin 130) : Prop :=
  (scaledValue (zeroLeft i) < 0 ∧ 0 < scaledValue (zeroRight i)) ∨
  (scaledValue (zeroRight i) < 0 ∧ 0 < scaledValue (zeroLeft i))

instance (i : Fin 130) : Decidable (branchScaledSign i) := inferInstanceAs (Decidable (_ ∨ _))
instance (i : Fin 130) : Decidable (zeroScaledSign i) := inferInstanceAs (Decidable (_ ∨ _))

end CatalanMeasure.Refinement.Trimmed130

-- Exported declaration axiom audit (local port).
#print axioms CatalanMeasure.Refinement.Trimmed130.signIndex
#print axioms CatalanMeasure.Refinement.Trimmed130.signIndex_surjective
#print axioms CatalanMeasure.Refinement.Trimmed130.branchScaledSign
#print axioms CatalanMeasure.Refinement.Trimmed130.zeroScaledSign
