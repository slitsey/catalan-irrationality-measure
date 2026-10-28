module

public import CatalanCore.Uniform.Content.UFFamily3.Thirds

@[expose] public section

namespace CatalanCore.Uniform.Content.UFFamily3

/-! Axiom audit and non-vacuity witnesses (lane H, H12). -/

example : F0.Reg 102 397 := by constructor <;> omega
example : F3.Reg 100 151 := by constructor <;> omega
example : F4.Reg 100 139 := by constructor <;> omega
example : F7.Reg 100 97 := by constructor <;> omega
example : F10.Reg 106 79 := by constructor <;> omega
example : F11.Reg 100 67 := by constructor <;> omega

#print axioms CatalanCore.Uniform.Content.UFFamily3.fiber_std
#print axioms CatalanCore.Uniform.Content.UFFamily3.killRunCert
#print axioms CatalanCore.Uniform.Content.UFFamily3.altKillRun
#print axioms CatalanCore.Uniform.Content.UFFamily3.cell3Gen_bound
#print axioms CatalanCore.Uniform.Content.UFFamily3.Cell3.price_le
#print axioms CatalanCore.Uniform.Content.UFFamily3.kill_of_pair
#print axioms CatalanCore.Uniform.Content.UFFamily3.thirdsUFLayer
#print axioms CatalanCore.Uniform.Content.UFFamily3.thirdsUFLayer_eff
#print axioms CatalanCore.Uniform.Content.UFFamily3.cellOf_bound
#print axioms CatalanCore.Uniform.Content.UFFamily3.F0.cell_bound
#print axioms CatalanCore.Uniform.Content.UFFamily3.F51.cell_bound
#print axioms CatalanCore.Uniform.Content.UFFamily3.pair_1_0_0_0_1

end CatalanCore.Uniform.Content.UFFamily3
