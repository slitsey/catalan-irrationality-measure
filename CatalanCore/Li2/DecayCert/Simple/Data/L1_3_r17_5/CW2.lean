module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_3_r17_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_3_r17_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c051_ok : WCell.ok source logs c051=true := by decide +kernel
theorem c052_ok : WCell.ok source logs c052=true := by decide +kernel
theorem c017_ok : WCell.ok source logs c017=true := by decide +kernel
theorem c026_ok : WCell.ok source logs c026=true := by decide +kernel
theorem c033_ok : WCell.ok source logs c033=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_3_r17_5
