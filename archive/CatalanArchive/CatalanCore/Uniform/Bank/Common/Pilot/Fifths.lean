import CatalanCore.Uniform.Bank.Common.Data.Fifths.Data

/-! Pilot (lane B, B0), generated: D5's elementary checker `basicOk` on the Fifths bank data, timed per declaration. -/

namespace CatalanCore.Uniform.Bank.Common.Pilot.Fifths

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Common.Data.Fifths

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 5

theorem fifths_segOk : ((List.finRange data.n).all data.segOk) = true := by decide +kernel
theorem fifths_conjOk : ((List.finRange data.n).all data.conjOk) = true := by decide +kernel
theorem fifths_mass : (∑ i : Fin data.n, SplineData.massOf (data.l i) = 1) := by decide +kernel
theorem fifths_loss : (315 / 100 : ℚ) * data.rho * data.BsQ ≤ data.lossS := by decide +kernel
theorem fifths_rayCover : coverOk 0 data.umax data.rayBoxes = true := by decide +kernel
theorem fifths_lineCover : coverOk 0 1 data.lineCells = true := by decide +kernel
theorem fifths_dof : data.dofOk = true := by decide +kernel
theorem fifths_basicOk : data.basicOk = true := by decide +kernel

end CatalanCore.Uniform.Bank.Common.Pilot.Fifths
