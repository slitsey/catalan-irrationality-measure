module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.GenD.Uniform.Bank532.Hosts532Inst

public section

/-!
Proof of the statement in `Challenge.lean`: the 532 bound of
`CatalanMeasure.GenD.Uniform.Bank532.catalan_irrationalityMeasure_532`.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_532 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(532 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.GenD.Uniform.Bank532.catalan_irrationalityMeasure_532

#print axioms catalan_irrationalityMeasure_532

end CatalanIrrationalityMeasure
