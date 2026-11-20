module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! The Lai challenge statements (plane `a ζ(3) + b ζ(4)` and the ratio `ζ(3)/π⁴`).  The proof
placeholders are intentional; the complete proofs are supplied separately in SolutionLai. -/

namespace LaiIrrationalityMeasure

/-- Plane: for every integer pair `(a, b)` with `b ≠ 0`, `μ(a ζ(3) + b ζ(4)) ≤ 27.49`. -/
theorem lai_plane_measure_27_49 (a b : ℤ) (hb : b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(27.49 : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) +
          (b : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 4)) - (p : ℝ) / q| := by
  sorry

/-- Ratio: `μ(ζ(3)/π⁴) ≤ 35.35`. -/
theorem lai_ratio_measure_35_35 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(35.35 : ℝ)) <
        |(∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) / Real.pi ^ 4 - (p : ℝ) / q| := by
  sorry

end LaiIrrationalityMeasure
