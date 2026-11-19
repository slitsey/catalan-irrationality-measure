module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_8_r22_0.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_8_r22_0
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logC15_ok : logC15.all logEntryOK=true := by decide +kernel
theorem logC16_ok : logC16.all logEntryOK=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_8_r22_0
