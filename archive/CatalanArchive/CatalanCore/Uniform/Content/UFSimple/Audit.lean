module

public import CatalanCore.Uniform.Content.UFSimple.Closed

/-!
# UF simplification (H18): axiom audit
-/

open CatalanCore.Uniform.Content.UFSimple

#print axioms fibCross_xK_ne
#print axioms cross_psiP_ne
#print axioms V_ne_of_sing
#print axioms card_union_window
#print axioms wedgeC_ne_of_V
#print axioms wedgeR_ne_of_V
#print axioms altWedgeC_ne_of_sep
#print axioms altWedgeR_ne_of_sep
#print axioms cellNo_bound
#print axioms cellExt_bound
#print axioms noSing_blk
#print axioms exists_datum_gen
#print axioms exists_datum_cand
#print axioms exists_datum_closed
#print axioms ufClosedLayer
#print axioms ufClosedLayer_base

/-- Non-vacuity of the closed price (thirds-like numbers: `m = 450`, `r = 3000`, `p = 1013`,
`ρ = 676`): the best candidate beats the trivial price `2 (r + m)`. -/
example : closedPrice 450 3000 1013 676 < 2 * (3000 + 450) := by decide
