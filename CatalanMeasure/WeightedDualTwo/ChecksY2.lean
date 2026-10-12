module

public import CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_36 : okY ((281 / 500 : ℚ), (728033 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_37 : okY ((728033 / 1250000 : ℚ), (5824267 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_38 : okY ((5824267 / 10000000 : ℚ), (5 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_39 : okY ((5 / 8 : ℚ), (1258599 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_40 : okY ((1258599 / 2000000 : ℚ), (6292997 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_41 : okY ((6292997 / 10000000 : ℚ), (1313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_42 : okY ((1313 / 2000 : ℚ), (6758177 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_43 : okY ((6758177 / 10000000 : ℚ), (6758179 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_44 : okY ((6758179 / 10000000 : ℚ), (86 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_45 : okY ((86 / 125 : ℚ), (7197129 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_46 : okY ((7197129 / 10000000 : ℚ), (7197131 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_47 : okY ((7197131 / 10000000 : ℚ), (3 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_48 : okY ((3 / 4 : ℚ), (3799537 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_49 : okY ((3799537 / 5000000 : ℚ), (1899769 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_50 : okY ((1899769 / 2500000 : ℚ), (781 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_51 : okY ((781 / 1000 : ℚ), (125107 / 156250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_52 : okY ((125107 / 156250 : ℚ), (160137 / 200000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_53 : okY ((160137 / 200000 : ℚ), (203 / 250 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
