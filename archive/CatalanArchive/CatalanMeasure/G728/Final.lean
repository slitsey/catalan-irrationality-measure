module
public import CatalanArchive.CatalanMeasure.G728.FinalGen
public import CatalanMeasure.G728.Cert.XCover
public import CatalanMeasure.G728.Cert.YCover
public import CatalanMeasure.G728.Cert.RCover
@[expose] public section
/-! The 728 bound: `FinalGen` applied to the three kernel-checked field sups. -/
namespace CatalanMeasure.G728
open OAI.InternalCatalan Filter

theorem catalan_irrationalityMeasure_728 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_728_of_sups row_sup column_sup residual_sup

end CatalanMeasure.G728
