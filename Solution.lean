module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.GenD.Signed.RouteI.Measure270

public section

/-!
Proof of the statement in `Challenge.lean`: the 270 bound of
`CatalanMeasure.GenD.Signed.RouteI.Measure270.catalan_irrationalityMeasure_270`.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_270 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(270 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.GenD.Signed.RouteI.Measure270.catalan_irrationalityMeasure_270

#print axioms catalan_irrationalityMeasure_270

end CatalanIrrationalityMeasure
