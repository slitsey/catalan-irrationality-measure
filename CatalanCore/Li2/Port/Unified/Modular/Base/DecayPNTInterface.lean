/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/DecayPNTInterface.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module

public import PrimeNumberTheoremAnd.Catalan.Consequences

@[expose] public section

theorem CatalanCore.Li2.Port.Li2.theta_isEquivalent_id :
    Asymptotics.IsEquivalent Filter.atTop Chebyshev.theta id :=
  CatalanPNT.chebyshev_asymptotic

#print axioms CatalanCore.Li2.Port.Li2.theta_isEquivalent_id
