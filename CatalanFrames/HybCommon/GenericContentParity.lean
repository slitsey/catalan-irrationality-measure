module

public import CatalanFrames.HybCommon.GenericTropBridge
public import CatalanFrames.HybCommon.DeficitProfile.MergedRows

@[expose] public section

/-! # Exact content targets for the prepared generic migration

Instance checks only. These preserve the current finite-table constant and
merged content price. The paper's untruncated tropical formula is checked
separately and is not identified with the finite-table majorant.
-/

open CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon.GenericContentParity

/-- The current finite table total, shared by both offset assignments. -/
theorem finite_table_total :
    ((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 +
      ((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 =
        24994314577 / 6665218560 := const8

/-- The paper's untruncated formula remains parameterized by the border ratio. -/
noncomputable def tropicalFormula (α : ℝ) : ℝ :=
  313 / 105 + (554 / 105) * α + (118 / 21 + 2 * Real.log 2) * α^2

lemma tropicalFormula_square : tropicalFormula 0 = 313 / 105 := by
  norm_num [tropicalFormula]

lemma tropicalFormula_eighth :
    tropicalFormula (1 / 8) = 12527 / 3360 + Real.log 2 / 32 := by
  unfold tropicalFormula
  ring

/-- No rounding or substitution of a different price is allowed in the port. -/
theorem merged_price : mergedLambda = 2015079667893797 / 547747200000000 := rfl

theorem merged_budget :
    baseLambda - profileIntegralL mergedProfile ≤
      2015079667893797 / 547747200000000 := mergedProfile_integral

#print axioms finite_table_total
#print axioms merged_budget

end CatalanFrames.HybCommon.GenericContentParity
