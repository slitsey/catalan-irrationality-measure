module

public import CatalanMeasure.Parametric.TwentyCostMain
public import CatalanMeasure.Parametric.SecondaryTentMain
public import CatalanMeasure.Parametric.SecondaryTentChebyshev
public import CatalanMeasure.Parametric.GapMain

public section

/-!
# Proofs of the advertised statements

The strongest statements of `Challenge.lean` are proved by
`CatalanMeasure.Parametric.catalan_irrationalityMeasure_878` and
`CatalanMeasure.Parametric.catalan_irrationalityMeasure_2632` in `GapMain.lean`.
The earlier `955`, `2864`, `1091`, `1095`, `1099` and `3662` statements
remain available from the retained secondary-tent and twenty-row proofs, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_878 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(878 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_878

/-- Chebyshev final prime selection with the PNT-backed denominator and content estimates. -/
theorem catalan_irrationalityMeasure_2632 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2632 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_2632

theorem catalan_irrationalityMeasure_955 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(955 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_955

/-- The previously published1091 statement remains available. -/
theorem catalan_irrationalityMeasure_1091 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(1091 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_1091

/-- The previously published1095 statement remains available. -/
theorem catalan_irrationalityMeasure_1095 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(1095 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_1095

/-- The previously published1099 statement remains available. -/
theorem catalan_irrationalityMeasure_1099 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(1099 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_1099

/-- Chebyshev final prime selection with the PNT-backed content estimate. -/
theorem catalan_irrationalityMeasure_2864 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2864 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_2864

/-- The previously published Chebyshev final-selection bound remains available. -/
theorem catalan_irrationalityMeasure_3662 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3662 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_3662

end CatalanIrrationalityMeasure
