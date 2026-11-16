module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! The ζ(5) challenge statement. The proof placeholder is intentional;
the complete proof is supplied separately in SolutionZeta5. -/

namespace Zeta5IrrationalityMeasure

theorem zeta5_irrationalityMeasure_87 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(87 : ℝ)) < |(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5) - (p : ℝ) / q| := by
  sorry

end Zeta5IrrationalityMeasure
