import CatalanCore.Uniform.Bank.Common.Data.Thirds.Data

/-! Pilot (lane B, B0), generated: D5's elementary checker `basicOk` on the Thirds bank data, timed per declaration. -/

namespace CatalanCore.Uniform.Bank.Common.Pilot.Thirds

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Common.Data.Thirds

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 5

theorem thirds_segOk : ((List.finRange data.n).all data.segOk) = true := by decide +kernel
theorem thirds_conjOk : ((List.finRange data.n).all data.conjOk) = true := by decide +kernel
theorem thirds_mass : (∑ i : Fin data.n, SplineData.massOf (data.l i) = 1) := by decide +kernel
theorem thirds_loss : (315 / 100 : ℚ) * data.rho * data.BsQ ≤ data.lossS := by decide +kernel
theorem thirds_rayCover : coverOk 0 data.umax data.rayBoxes = true := by decide +kernel
theorem thirds_lineCover : coverOk 0 1 data.lineCells = true := by decide +kernel
theorem thirds_dof : data.dofOk = true := by decide +kernel
theorem thirds_basicOk : data.basicOk = true := by decide +kernel

end CatalanCore.Uniform.Bank.Common.Pilot.Thirds
