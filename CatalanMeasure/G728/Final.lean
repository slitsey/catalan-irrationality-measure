module
public import CatalanMeasure.G728.FinalGen
public import CatalanMeasure.G728.Cert.XCover
public import CatalanMeasure.G728.Cert.YCover
public import CatalanMeasure.G728.Cert.RCover
@[expose] public section
/-! The 728 and 2183 bounds: `FinalGen` applied to the three kernel-checked field sups. -/
namespace CatalanMeasure.G728
open OAI.InternalCatalan Filter

theorem catalan_irrationalityMeasure_728 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_728_of_sups row_sup column_sup residual_sup

theorem catalan_irrationalityMeasure_2183 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(2183 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_2183_of_sups row_sup column_sup residual_sup

end CatalanMeasure.G728
