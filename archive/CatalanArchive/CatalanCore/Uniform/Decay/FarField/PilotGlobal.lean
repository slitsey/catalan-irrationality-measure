import CatalanCore.Uniform.Decay.FarField.PilotData
set_option Elab.async false
set_option maxRecDepth 100000

/-! The global far-field check of the chi3 trial measure (lane D, D15): the claimed moments equal
the exact moments, the total weighted mass is zero, the total variation is at most `5/2`, and all
segment endpoints lie in the disc `|z - 1/2| ≤ 1`. -/

namespace CatalanCore.Uniform.Bank.Chi3.FarPilot
open CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.FarField

theorem far_global : mpGlobalOk (cellPieces Dn nuC) Mfar = true := by decide +kernel

end CatalanCore.Uniform.Bank.Chi3.FarPilot
