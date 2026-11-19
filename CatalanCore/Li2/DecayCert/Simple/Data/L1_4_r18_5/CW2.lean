module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c051_ok : WCell.ok source logs c051=true := by decide +kernel
theorem c052_ok : WCell.ok source logs c052=true := by decide +kernel
theorem c016_ok : WCell.ok source logs c016=true := by decide +kernel
theorem c023_ok : WCell.ok source logs c023=true := by decide +kernel
theorem c032_ok : WCell.ok source logs c032=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_4_r18_5
