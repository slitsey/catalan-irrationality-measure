module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_0 : okY ((0 : ℚ), (44131 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_1 : okY ((44131 / 2000000 : ℚ), (220657 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_2 : okY ((220657 / 10000000 : ℚ), (31 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_3 : okY ((31 / 1000 : ℚ), (73057 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_4 : okY ((73057 / 2000000 : ℚ), (365287 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_5 : okY ((365287 / 10000000 : ℚ), (31 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_6 : okY ((31 / 500 : ℚ), (696311 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_7 : okY ((696311 / 10000000 : ℚ), (696313 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_8 : okY ((696313 / 10000000 : ℚ), (187 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_9 : okY ((187 / 2000 : ℚ), (1007501 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_10 : okY ((1007501 / 10000000 : ℚ), (62969 / 625000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_11 : okY ((62969 / 625000 : ℚ), (1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_12 : okY ((1 / 8 : ℚ), (757893 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_13 : okY ((757893 / 5000000 : ℚ), (378947 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_14 : okY ((378947 / 2500000 : ℚ), (47 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_15 : okY ((47 / 250 : ℚ), (1960531 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_16 : okY ((1960531 / 10000000 : ℚ), (1960533 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_17 : okY ((1960533 / 10000000 : ℚ), (1 / 4 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
