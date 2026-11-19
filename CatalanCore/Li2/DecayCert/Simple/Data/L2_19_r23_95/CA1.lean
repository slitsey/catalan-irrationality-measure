module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_19_r23_95.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_19_r23_95
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c054_ok : ACell.ok (setup.sourceAt pair.rho) logs c054=true := by decide +kernel
theorem c059_ok : ACell.ok (setup.sourceAt pair.rho) logs c059=true := by decide +kernel
theorem c065_ok : ACell.ok (setup.sourceAt pair.rho) logs c065=true := by decide +kernel
theorem c070_ok : ACell.ok (setup.sourceAt pair.rho) logs c070=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_19_r23_95
