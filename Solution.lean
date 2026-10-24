module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.GenD.D58.Main590

public section

/-!
Proof of the statement in `Challenge.lean`: the 590 bound of
`CatalanMeasure.GenD.D58.catalan_irrationalityMeasure_590`.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_590 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(590 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.GenD.D58.catalan_irrationalityMeasure_590

#print axioms catalan_irrationalityMeasure_590

end CatalanIrrationalityMeasure
