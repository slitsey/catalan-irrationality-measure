module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-!
# An irrationality measure for Catalan's constant

Catalan's constant is `G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`; it is written out below as a `tsum`
(the series converges absolutely, so the `tsum` is its sum).

The two statements say that for every sufficiently large denominator `b` and every integer
numerator `a`,

* `|G - a / b| > b ^ (-34000)` (so the irrationality exponent of `G` is at most `34000`), and
* `|G - a / b| > b ^ (-100800)`, the bound obtained with Chebyshev's estimates in place of the
  prime number theorem in the final step.

Reference: S. Litsey, *An irrationality measure for Catalan's constant* (2026), building on
OpenAI, *Catalan's constant is irrational* (2026).
-/

namespace CatalanIrrationalityMeasure

/-- **Irrationality measure for Catalan's constant.** For all sufficiently large natural
numbers `b` and all integers `a`, `b ^ (-34000) < |G - a / b|`, where
`G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`.  Hence `μ(G) ≤ 34000`. -/
theorem catalan_irrationalityMeasure_34000 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(34000 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same statement with exponent `100800`, which the argument gives when the prime number
theorem is replaced by Chebyshev's bounds in the final step. -/
theorem catalan_irrationalityMeasure_100800 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(100800 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

end CatalanIrrationalityMeasure
