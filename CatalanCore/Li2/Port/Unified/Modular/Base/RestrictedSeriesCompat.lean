/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/RestrictedSeriesCompat.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import Mathlib.RingTheory.PowerSeries.Restricted

@[expose] public section

namespace CatalanCore.Li2.Port.Li2

/-- Scalar multiplication preserves restricted power series. -/
lemma restrictedSeries_smul {R : Type*} [NormedRing R] [IsUltrametricDist R]
    (c : ℝ) {f : PowerSeries R} (hf : PowerSeries.IsRestricted c f) (a : R) :
    PowerSeries.IsRestricted c (a • f) := by
  rw [PowerSeries.smul_eq_C_mul]
  exact PowerSeries.isRestricted.mul c (PowerSeries.isRestricted_C c a) hf

end CatalanCore.Li2.Port.Li2
end
