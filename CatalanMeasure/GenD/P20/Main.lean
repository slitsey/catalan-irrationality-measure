module

public import CatalanMeasure.GenD.P20.Measure

@[expose] public section

/-!
# The 728 bound: thin wrapper over the generic layer

Same name and statement as the former `CatalanMeasure.G728.Final` theorem; the proof is
`measure_of_design` at `(20, 3, 1, 2, 1)` (`GenD.P20.Measure`).
-/

namespace CatalanMeasure.G728
open OAI.InternalCatalan Filter

theorem catalan_irrationalityMeasure_728 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| :=
  CatalanMeasure.GenD.P20.measure_728

#print axioms catalan_irrationalityMeasure_728

end CatalanMeasure.G728
