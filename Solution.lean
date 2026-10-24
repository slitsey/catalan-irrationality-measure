module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.GenD.P20.Main

public section

/-!
Proof of the statement in `Challenge.lean`: the 728 bound of `CatalanMeasure.G728`.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_728 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(728 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.G728.catalan_irrationalityMeasure_728

#print axioms catalan_irrationalityMeasure_728

end CatalanIrrationalityMeasure
