module

public import CatalanMeasure.Parametric.TwentySharperMain

#print axioms CatalanMeasure.Parametric.twenty_measure_sharper_eta_lt
#print axioms CatalanMeasure.Parametric.catalan_irrationalityMeasure_1095

example : ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
    (b : ℝ) ^ (-(1095 : ℝ)) <
      |OAI.InternalCatalan.catalan - (a : ℝ) / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_1095
