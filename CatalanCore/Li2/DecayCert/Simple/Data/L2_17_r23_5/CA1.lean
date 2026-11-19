module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_17_r23_5.Defs
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_17_r23_5
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem c090_ok : ACell.ok (setup.sourceAt pair.rho) logs c090=true := by decide +kernel
theorem c072_ok : ACell.ok (setup.sourceAt pair.rho) logs c072=true := by decide +kernel
theorem c077_ok : ACell.ok (setup.sourceAt pair.rho) logs c077=true := by decide +kernel
theorem c084_ok : ACell.ok (setup.sourceAt pair.rho) logs c084=true := by decide +kernel
theorem c089_ok : ACell.ok (setup.sourceAt pair.rho) logs c089=true := by decide +kernel
end CatalanCore.Li2.DecayCert.Simple.Data.L2_17_r23_5
