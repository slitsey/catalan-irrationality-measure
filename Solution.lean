module

public import CatalanMeasure.Parametric.TwentyCostMain

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`CatalanMeasure.Parametric.catalan_irrationalityMeasure_1091` and
`CatalanMeasure.Parametric.catalan_irrationalityMeasure_3662` of
`TwentyCostMain.lean` and the retained `TwentyMain.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

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

theorem catalan_irrationalityMeasure_3662 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(3662 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_3662

end CatalanIrrationalityMeasure
