module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r28_0.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r28_0
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logC10_ok : logC10.all logEntryOK=true := by decide +kernel
theorem logC11_ok : logC11.all logEntryOK=true := by decide +kernel
theorem logC12_ok : logC12.all logEntryOK=true := by decide +kernel
theorem logC13_ok : logC13.all logEntryOK=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r28_0
