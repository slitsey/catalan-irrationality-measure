module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! The Lai challenge statements (plane `a ζ(3) + b ζ(4)` and the ratio `ζ(3)/π⁴`).  The proof
placeholders are intentional; the complete proofs are supplied separately in SolutionLai. -/

namespace LaiIrrationalityMeasure

/-- Plane: for every integer pair `(a, b)` with `b ≠ 0`, `μ(a ζ(3) + b ζ(4)) ≤ 34.14`. -/
theorem lai_plane_measure_34_14 (a b : ℤ) (hb : b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(34.14 : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) +
          (b : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 4)) - (p : ℝ) / q| := by
  sorry

/-- Ratio: `μ(ζ(3)/π⁴) ≤ 55.50`. -/
theorem lai_ratio_measure_55_50 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) <
        |(∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) / Real.pi ^ 4 - (p : ℝ) / q| := by
  sorry

/-- Ratios: for integers `a, b, c, d` with `a d - b c ≠ 0`,
`μ((a ζ(3) + b π⁴)/(c ζ(3) + d π⁴)) ≤ 55.50`. -/
theorem lai_ratio_mobius_measure_55_50 (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) + (b : ℝ) * Real.pi ^ 4) /
            ((c : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) + (d : ℝ) * Real.pi ^ 4) - (p : ℝ) / q| := by
  sorry

end LaiIrrationalityMeasure
