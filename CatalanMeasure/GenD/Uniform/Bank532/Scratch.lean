module

public import CatalanMeasure.GenD.Uniform.Bank535.Ledger10.Merge13

@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.Bank532
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank535.Ledger10 CatalanMeasure.GenD.Uniform.LedgerW
noncomputable section

example : wins13.getD 0 (cw 0 0 0 0) = cw (16/7:ℝ) (23/10:ℝ) (-16:ℝ) (7:ℝ) := rfl
example : wins13.getD 40 (cw 0 0 0 0) = cw (67779/10000:ℝ) (6857/1000:ℝ) (-61:ℝ) (9:ℝ) := rfl
example : wins13.getD 60 (cw 0 0 0 0) = cw (69/5:ℝ) (14:ℝ) (-6:ℝ) (1/2:ℝ) := rfl
example : wins13.getD 72 (cw 0 0 0 0) = cw (26:ℝ) (53/2:ℝ) (53:ℝ) (-2:ℝ) := rfl
example : wins13.length = 73 := rfl

end
end CatalanMeasure.GenD.Uniform.Bank532
