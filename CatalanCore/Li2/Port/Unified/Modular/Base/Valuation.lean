/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/Valuation.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module

public import CatalanCore.Zeta5.Local.Val

@[expose] public section

namespace CatalanCore.Li2.Port.Li2
export Apery (VG GV det_GV)
namespace VG
export Apery.VG (zero mono neg add sub mul sum prod intCast natCast one inv of_eq primePow zpow_mul pow inv_nat)
end VG
namespace GV
export Apery.GV (zero mono add neg sub C X mul C_mul sum prod)
end GV
end CatalanCore.Li2.Port.Li2

#print axioms CatalanCore.Li2.Port.Li2.det_GV
