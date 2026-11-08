module

public import CatalanCore.Uniform.Bank.Sevenths.NV
public import CatalanCore.Uniform.Content.Shape.Reindex
public import CatalanCore.Measure.Scaling

@[expose] public section
set_option Elab.async false

/-! Conditional sevenths assembly on the new alternating family.
The content and decay suppliers remain explicit obligations. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

/-- The exact content constant of the sevenths bank. -/
noncomputable def Lam7 : ℝ :=
  8926987763346083870538925313134246938568387 / 2458710375447819602863559629392237970329600 + (1 / 72) * Real.log 2

/-- The directed decay rate. -/
def D7 : ℚ := 819725632032648948973739 / 225000000000000000000000

/-- The directed decay constant. -/
def c7 : ℚ := 37109307686511727 / 5000000000000000

theorem Lam7_lt_D7 : Lam7 < (D7 : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold Lam7 D7
  push_cast
  nlinarith

end CatalanCore.Uniform.Bank.Sevenths
