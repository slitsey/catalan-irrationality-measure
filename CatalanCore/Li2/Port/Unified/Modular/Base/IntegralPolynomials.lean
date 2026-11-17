/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/IntegralPolynomials.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: C7 canonical Apery valuation extensions with declaration-site exports; module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module

public import CatalanCore.Li2.Port.Unified.Modular.Base.Valuation
public import CatalanCore.Zeta5.Local.IntPoly

@[expose] public section

namespace CatalanCore.Li2.Port.Li2
export Apery (factor_roots)
namespace GV
export Apery.GV (pow comp divByMonic_X_sub_C multiset_prod)
end GV
namespace VG
export Apery.VG (eval eval_zero)
end VG
end CatalanCore.Li2.Port.Li2

#print axioms Apery.GV.pow
#print axioms Apery.factor_roots
