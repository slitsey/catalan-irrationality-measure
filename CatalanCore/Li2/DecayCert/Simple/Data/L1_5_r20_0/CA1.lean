module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_5_r20_0.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_5_r20_0
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c128_ok : ACell.ok (setup.sourceAt pair.rho) logs c128=true := by decide +kernel
theorem c129_ok : ACell.ok (setup.sourceAt pair.rho) logs c129=true := by decide +kernel
theorem c127_ok : ACell.ok (setup.sourceAt pair.rho) logs c127=true := by decide +kernel
theorem c107_ok : ACell.ok (setup.sourceAt pair.rho) logs c107=true := by decide +kernel
theorem c112_ok : ACell.ok (setup.sourceAt pair.rho) logs c112=true := by decide +kernel
theorem c121_ok : ACell.ok (setup.sourceAt pair.rho) logs c121=true := by decide +kernel
theorem c126_ok : ACell.ok (setup.sourceAt pair.rho) logs c126=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_5_r20_0
