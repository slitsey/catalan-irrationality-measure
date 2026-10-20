module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-!
Catalan's constant is written as the series below.
For every sufficiently large denominator b and every integer numerator a,
|G - a/b| > b^(-740). Denominator and content asymptotics use PNT.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_740 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

end CatalanIrrationalityMeasure
