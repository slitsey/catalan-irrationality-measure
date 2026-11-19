module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2.Setup
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2.Pair
public import CatalanCore.Li2.DecayCert.TableSimple
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
/-- The SIMPLE lattice package of this datum and its pair certificate. -/
noncomputable def package : LatticeSimplePackage := ⟨z,input,setup,setup_ok⟩
theorem pair_checked : simplePairCheck package.setup pair=true := pair_ok
end CatalanCore.Li2.DecayCert.Simple.Data.L2_25_r25_2
