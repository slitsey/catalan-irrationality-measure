module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c101_ok : RCell.ok source logs c101=true := by decide +kernel
theorem c102_ok : RCell.ok source logs c102=true := by decide +kernel
theorem c103_ok : RCell.ok source logs c103=true := by decide +kernel
theorem c104_ok : RCell.ok source logs c104=true := by decide +kernel
theorem c105_ok : RCell.ok source logs c105=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5
