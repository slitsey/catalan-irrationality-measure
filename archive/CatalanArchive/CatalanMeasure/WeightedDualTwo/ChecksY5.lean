module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_90 : okY ((99951 / 100000 : ℚ), (199937 / 200000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_91 : okY ((199937 / 200000 : ℚ), (2499213 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_92 : okY ((2499213 / 2500000 : ℚ), (1 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
