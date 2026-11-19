module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r27_95.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r27_95
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logC00_ok : logC00.all logEntryOK=true := by decide +kernel
theorem logC01_ok : logC01.all logEntryOK=true := by decide +kernel
theorem logC02_ok : logC02.all logEntryOK=true := by decide +kernel
theorem logC03_ok : logC03.all logEntryOK=true := by decide +kernel
theorem logC04_ok : logC04.all logEntryOK=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_37_r27_95
