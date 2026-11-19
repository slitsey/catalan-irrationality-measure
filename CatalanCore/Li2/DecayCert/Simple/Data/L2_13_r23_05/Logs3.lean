module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_13_r23_05.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_13_r23_05
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logC15_ok : logC15.all logEntryOK=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_13_r23_05
