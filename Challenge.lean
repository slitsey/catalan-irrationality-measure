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

* `|G - a / b| > b ^ (-2742)` (so the irrationality exponent of `G` is at most `2742`), and
* `|G - a / b| > b ^ (-7675)`, the bound obtained with Chebyshev's estimates in place of the
  prime number theorem in the final step.

Reference: S. Litsey, *An irrationality measure for Catalan's constant* (2026), building on
OpenAI, *Catalan's constant is irrational* (2026).
-/

namespace CatalanIrrationalityMeasure

/-- **Irrationality measure for Catalan's constant.** For all sufficiently large natural
numbers `b` and all integers `a`, `b ^ (-2742) < |G - a / b|`, where
`G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`.  Hence `μ(G) ≤ 2742`. -/
theorem catalan_irrationalityMeasure_2742 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2742 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

/-- The same statement with exponent `7675`, which the argument gives when the prime number
theorem is replaced by Chebyshev's bounds in the final step. -/
theorem catalan_irrationalityMeasure_7675 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(7675 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  sorry

end CatalanIrrationalityMeasure
