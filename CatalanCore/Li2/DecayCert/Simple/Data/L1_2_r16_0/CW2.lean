module
public import CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r16_0.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r16_0
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c052_ok : WCell.ok source logs c052=true := by decide +kernel
theorem c053_ok : WCell.ok source logs c053=true := by decide +kernel
theorem c054_ok : WCell.ok source logs c054=true := by decide +kernel
theorem c004_ok : WCell.ok source logs c004=true := by decide +kernel
theorem c016_ok : WCell.ok source logs c016=true := by decide +kernel
theorem c022_ok : WCell.ok source logs c022=true := by decide +kernel
theorem c030_ok : WCell.ok source logs c030=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r16_0
