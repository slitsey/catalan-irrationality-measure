module

public import OAI.NumberTheory.Catalan.Estimates.ExceptionalScalarBounds

@[expose] public section

namespace OAI


noncomputable section

namespace InternalCatalan

def discrepancyNormFactor (z : ℚ) : ℝ :=
  max 1 (max ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ‖smoothingMoment 0 1‖)

theorem one_le_discrepancyNormFactor (z : ℚ) : 1 ≤ discrepancyNormFactor z :=
  le_max_left _ _

theorem discrepancyNormFactor_nonneg (z : ℚ) : 0 ≤ discrepancyNormFactor z :=
  zero_le_one.trans (one_le_discrepancyNormFactor z)

end InternalCatalan

end

end OAI
