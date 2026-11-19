module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_33_r24_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_33_r24_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c062_ok : ACell.ok (setup.sourceAt pair.rho) logs c062=true := by decide +kernel
theorem c067_ok : ACell.ok (setup.sourceAt pair.rho) logs c067=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_33_r24_5
