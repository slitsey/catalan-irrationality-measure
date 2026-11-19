module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_23_r24_8.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_23_r24_8
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c068_ok : ACell.ok (setup.sourceAt pair.rho) logs c068=true := by decide +kernel
theorem c073_ok : ACell.ok (setup.sourceAt pair.rho) logs c073=true := by decide +kernel
theorem c079_ok : ACell.ok (setup.sourceAt pair.rho) logs c079=true := by decide +kernel
theorem c085_ok : ACell.ok (setup.sourceAt pair.rho) logs c085=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_23_r24_8
