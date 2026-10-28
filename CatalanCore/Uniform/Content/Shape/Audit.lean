module

public import CatalanCore.Uniform.Content.Shape.Wrap
public import CatalanCore.Uniform.Content.Shape.Alt

@[expose] public section

/-! Axiom audit for lane H7 (Shape), with a concrete instance of the alternating geometry. -/

open CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire

/-- Concrete test: `c = 1/4` (so alpha = 1/8), scale `r = 64`. -/
theorem altGeom_test : HybShape (altGeom (1 / 4) (by norm_num)) 64 :=
  altGeom_hybShape (1 / 4) (by norm_num) (by norm_num)

#print axioms Content.Shape.keepNodes_image_range
#print axioms Content.Shape.altGeom_hybShape
#print axioms altGeom_test
#print axioms measure_of_family_nv0_even
#print axioms Content.Shape.hasContent_of_debitLayers_on
#print axioms Content.Shape.hasContent_twoTerm_on
#print axioms Content.Shape.hasContent_multiTerm_on
#print axioms BlockGeom.measure_of_providers_even
