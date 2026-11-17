module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace CatalanCore.Li2

/-- Content rate for a rational argument, in the general Li₂ measure contract. -/
noncomputable def cRate (a b : ℤ) : ℝ :=
  7 / 2 - 523 / 840 + (8 / 3) * Real.log (b : ℝ) -
    6 * Real.log |(a : ℝ)| - (9 / 4) * Real.log |((b - a : ℤ) : ℝ)|

end CatalanCore.Li2

#print axioms CatalanCore.Li2.cRate