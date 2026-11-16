module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanCore.Zeta5.Data.Public

public section

/-!
The irrationality measure `μ(ζ(5)) ≤ 87`: for all sufficiently large `q` and all integers `p`,
`|ζ(5) - p/q| > q^(-87)`.
-/

namespace Zeta5IrrationalityMeasure

theorem zeta5_irrationalityMeasure_87 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(87 : ℝ)) < |(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5) - (p : ℝ) / q| :=
  CatalanCore.Zeta5.Data.Public.zeta5_irrationalityMeasure_87

#print axioms zeta5_irrationalityMeasure_87

end Zeta5IrrationalityMeasure
