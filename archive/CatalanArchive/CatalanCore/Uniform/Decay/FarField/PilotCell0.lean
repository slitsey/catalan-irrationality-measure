import CatalanCore.Uniform.Decay.FarField.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! Far-field cell `[0, 1/16]` of the chi3 tube edge 7 (lane D, D15). -/

namespace CatalanCore.Uniform.Bank.Chi3.FarPilot
open CatalanCore.Uniform.Decay.FarField

theorem ok_fc0 : cellOk3 nuC Mfar Rtw eWc ePc Fc Dn e7 fc0 = true := by decide +kernel

end CatalanCore.Uniform.Bank.Chi3.FarPilot
