module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logC20_ok : logC20.all logEntryOK=true := by decide +kernel
theorem logC21_ok : logC21.all logEntryOK=true := by decide +kernel
theorem logC22_ok : logC22.all logEntryOK=true := by decide +kernel
theorem logC23_ok : logC23.all logEntryOK=true := by decide +kernel
theorem logC24_ok : logC24.all logEntryOK=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r14_5
