module

public import CatalanCore.Zeta5.Data.Public

@[expose] public section

/-!
# Public names for the ζ(5) paper

Descriptive aliases, cited in the paper, for declarations whose source names carry ledger
identifiers.
-/

namespace Apery.CostIn
alias inner_cost_gamma := zc17_gammaIn
end Apery.CostIn

namespace Apery.ExtHyp
alias outer_extension := zc18_ext
end Apery.ExtHyp

namespace CatalanCore.Zeta5.CostOut
alias outer_ext_gamma := zc19_gamma
alias outer_ext_cost := zc19_cost
alias outer_cost := zc20_outer
end CatalanCore.Zeta5.CostOut

namespace CatalanCore.Zeta5.Sum
alias integral_T0 := zc34
alias integral_head := zc35
alias integral_R_mid := zc36
alias integral_R_tail := zc37
alias integral_gref := zc38
end CatalanCore.Zeta5.Sum

namespace CatalanCore.Zeta5.Content
alias content_bound_signed := zc32_signed
alias normaliser_bound := zc32_normaliser
end CatalanCore.Zeta5.Content

namespace CatalanCore.Zeta5.Cells
alias energy_const_sound := zd22_sound
end CatalanCore.Zeta5.Cells
