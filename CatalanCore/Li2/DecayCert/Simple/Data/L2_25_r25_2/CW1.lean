module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c025_ok : WCell.ok source logs c025=true := by decide +kernel
theorem c026_ok : WCell.ok source logs c026=true := by decide +kernel
theorem c027_ok : WCell.ok source logs c027=true := by decide +kernel
theorem c028_ok : WCell.ok source logs c028=true := by decide +kernel
theorem c015_ok : WCell.ok source logs c015=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2
