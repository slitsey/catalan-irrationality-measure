import CatalanCore.Uniform.Bank.Common.Data.Lambda.Data

/-! Pilot (lane B, B0), generated: D5's elementary checker `basicOk` on the Lambda bank data, timed per declaration. -/

namespace CatalanCore.Uniform.Bank.Common.Pilot.Lambda

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Common.Data.Lambda

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 5

theorem lambda_segOk : ((List.finRange data.n).all data.segOk) = true := by decide +kernel
theorem lambda_conjOk : ((List.finRange data.n).all data.conjOk) = true := by decide +kernel
theorem lambda_mass : (∑ i : Fin data.n, SplineData.massOf (data.l i) = 1) := by decide +kernel
theorem lambda_loss : (315 / 100 : ℚ) * data.rho * data.BsQ ≤ data.lossS := by decide +kernel
theorem lambda_rayCover : coverOk 0 data.umax data.rayBoxes = true := by decide +kernel
theorem lambda_lineCover : coverOk 0 1 data.lineCells = true := by decide +kernel
theorem lambda_dof : data.dofOk = true := by decide +kernel
theorem lambda_basicOk : data.basicOk = true := by decide +kernel

end CatalanCore.Uniform.Bank.Common.Pilot.Lambda
