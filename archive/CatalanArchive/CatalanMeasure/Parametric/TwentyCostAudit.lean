module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyCostMain

@[expose] public section

/-! Targeted dependency audit of the cost-parametric marked-atom chain. -/

#print axioms CatalanMeasure.Parametric.twenty_sharper_first_full_interval_budget
#print axioms CatalanMeasure.Parametric.twenty_first_cost_budget_sharp
#print axioms CatalanMeasure.Parametric.twenty_full_first_energy_of_cost_eventually
#print axioms CatalanMeasure.Parametric.twenty_first_marked_product_of_cost_eventually
#print axioms CatalanMeasure.Parametric.twenty_first_marked_sheet_product_of_cost_eventually
#print axioms CatalanMeasure.Parametric.twenty_marked_sheet_product_of_cost_eventually
#print axioms CatalanMeasure.Parametric.twenty_weighted_atom_point_of_cost
#print axioms CatalanMeasure.Parametric.twenty_weighted_atom_det_of_point_eventually
#print axioms CatalanMeasure.Parametric.twenty_joint_factor_of_cost_eventually
#print axioms CatalanMeasure.Parametric.twenty_perturbation_of_cost
#print axioms CatalanMeasure.Parametric.twentyMeasureIntPoly_cost_hypotheses
#print axioms CatalanMeasure.Parametric.twenty_atom_point_538_5
#print axioms CatalanMeasure.Parametric.catalan_irrationalityMeasure_1091

example : ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
    (b : ℝ) ^ (-(1091 : ℝ)) <
      |OAI.InternalCatalan.catalan - (a : ℝ) / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_1091
