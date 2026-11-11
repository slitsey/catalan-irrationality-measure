module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! The hybrid challenge statements. Proof placeholders are intentional;
the complete proofs are supplied separately in SolutionHybrid. -/

namespace TrigammaDifferences

theorem lambda_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((311973 / 10000 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
  sorry

theorem lambda_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((311973 / 10000 : ℚ) : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (a : ℝ) / b| := by
  sorry

theorem chi3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((136839 / 10000 : ℚ) : ℝ)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (a : ℝ) / b| := by
  sorry

theorem chi3_plus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((94913 / 10000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  sorry

theorem chi3_minus_pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((94913 / 10000 : ℚ) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (a : ℝ) / b| := by
  sorry

theorem fifths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem fifths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem fifths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem fifths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((59439 / 2500 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths1_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths4_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths5_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem sevenths6_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((18061719 / 10000 : ℚ) : ℝ)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (a : ℝ) / b| := by
  sorry

theorem pi2_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((32607 / 5000 : ℚ) : ℝ)) <
        |Real.pi ^ 2 - (a : ℝ) / b| := by
  sorry

theorem plane1_measure (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-((206622 / 10000 : ℚ) : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + (b : ℝ) * Real.pi ^ 2) - (p : ℝ) / q| := by
  sorry

theorem plane2_measure (a b : ℚ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-((33520 / 100 : ℚ) : ℝ)) <
        |((a : ℝ) * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) + (b : ℝ) * Real.pi ^ 2) - (p : ℝ) / q| := by
  sorry

theorem dip_2_27_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((14 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + 2 * Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  sorry

theorem dip_2_27_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((14 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - 2 * Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  sorry

theorem dip_1_27_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((15359 / 1000 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  sorry

theorem dip_1_27_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((15359 / 1000 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 27) - (a : ℝ) / b| := by
  sorry

theorem dip_1_18_plus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((4373 / 250 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 18) - (a : ℝ) / b| := by
  sorry

theorem dip_1_18_minus_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(((4373 / 250 : ℚ)) : ℝ)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 18) - (a : ℝ) / b| := by
  sorry

theorem zeta3_measure :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-((60382 / 10000 : ℚ) : ℝ)) <
        |(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) - (a : ℝ) / b| := by
  sorry

theorem plane3_measure (a b : ℚ) (hab : a≠0 ∨ b≠0) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-(72.726:ℝ))<
      |((a:ℝ)*(∑' n : ℕ,1/((n:ℝ)+1)^3)+(b:ℝ)*Real.pi^4)-(p:ℝ)/q| := by
  sorry

end TrigammaDifferences
