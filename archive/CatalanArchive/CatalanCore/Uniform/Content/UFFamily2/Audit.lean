module

public import CatalanCore.Uniform.Content.UFFamily2.SevHLayer
public import CatalanCore.Uniform.Content.UFFamily2.SevH2

/-!
# Axiom audit of the `UFFamily2` package (lane H, H11)
-/

open CatalanCore.Uniform.Content.UFFamily2 CatalanCore.Uniform.Content.UFFamily2.SevH

#print axioms CatalanCore.Uniform.Content.UFFamily2.fiberList_range
#print axioms CatalanCore.Uniform.Content.UFFamily2.LuData.ok_spec
#print axioms CatalanCore.Uniform.Content.UFFamily2.LuData.crossZ_zmod_ne
#print axioms CatalanCore.Uniform.Content.UFFamily2.KillCert.ofLu
#print axioms CatalanCore.Uniform.Content.UFFamily2.not_dvd_or_of_bezout
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.cross_not_dvd
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.killH
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.hu_gen2
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.cellH
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.cellH_bound
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.layerH
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.layerH_eff
#print axioms CatalanCore.Uniform.Content.UFFamily2.cellGen
#print axioms CatalanCore.Uniform.Content.UFFamily2.cellGen_bound
#print axioms CatalanCore.Uniform.Content.UFFamily2.layerGen
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.winH
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.layerH2
#print axioms CatalanCore.Uniform.Content.UFFamily2.SevH.baseGen_eq_baseH

/-- Non-vacuity of the family: `r = 288`, `p = 173` (`m = 24`, `k₁ = 322`, border `[288, 336)`). -/
example : Valid 288 173 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩
example : k1 173 = 322 := by decide
/-- Price of the pilot cell: `baseH 288 173 = 590` against the trivial price `2 (r + m) = 624`. -/
example : baseH 288 173 = 590 := by decide
