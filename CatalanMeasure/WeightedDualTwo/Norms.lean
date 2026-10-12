module

public import CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem hNP : normOK Pc P NP = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hNV : normOK Vc V NV = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
