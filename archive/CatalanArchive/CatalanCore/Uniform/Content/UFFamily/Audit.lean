module

public import CatalanCore.Uniform.Content.UFFamily.SevELayer
public import CatalanCore.Uniform.Content.UFFamily.Parity
public import CatalanCore.Uniform.Content.UFFamily.DetPilot
public import CatalanCore.Uniform.Content.UFFamily.LuPilot
public import CatalanCore.Uniform.Content.UFFamily.LuSizes

/-!
# Axiom audit of the `UFFamily` package (lane H10)
-/

open CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE

#print axioms CatalanCore.Uniform.Content.UFFamily.good_V
#print axioms CatalanCore.Uniform.Content.UFFamily.good_W
#print axioms CatalanCore.Uniform.Content.UFFamily.nodeFib_realizes
#print axioms CatalanCore.Uniform.Content.UFFamily.KillCert.ofTypes
#print axioms CatalanCore.Uniform.Content.UFFamily.luOK_det
#print axioms CatalanCore.Uniform.Content.UFFamily.Parity.par13_val
#print axioms CatalanCore.Uniform.Content.UFFamily.Parity.par1_ok
#print axioms CatalanCore.Uniform.Content.UFFamily.DetPilot.luJA
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.killE
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.cellE
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.cellE_bound
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.layerE
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.layerE_eff
#print axioms CatalanCore.Uniform.Content.UFFamily.fibZ_eq_val
#print axioms CatalanCore.Uniform.Content.UFFamily.border_det
#print axioms CatalanCore.Uniform.Content.UFFamily.LuPilot.lcross_ne
#print axioms CatalanCore.Uniform.Content.UFFamily.SevE.layerE_base

/-- Non-vacuity of the family: `r = 144`, `p = 173` (`k₀ = 149`, border `[144, 168)`). -/
example : CatalanCore.Uniform.Content.UFFamily.SevE.Valid 144 173 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩
example : CatalanCore.Uniform.Content.UFFamily.SevE.k0 173 = 149 := by decide
