module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r15_0.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r15_0
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c104_ok : RCell.ok source logs c104=true := by decide +kernel
theorem c105_ok : RCell.ok source logs c105=true := by decide +kernel
theorem c106_ok : RCell.ok source logs c106=true := by decide +kernel
theorem c107_ok : RCell.ok source logs c107=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r15_0
