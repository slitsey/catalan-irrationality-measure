module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okY_18 : okY ((1 / 4 : ℚ), (2567739 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_19 : okY ((2567739 / 10000000 : ℚ), (2567741 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_20 : okY ((2567741 / 10000000 : ℚ), (281 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_21 : okY ((281 / 1000 : ℚ), (96067 / 312500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_22 : okY ((96067 / 312500 : ℚ), (1537073 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_23 : okY ((1537073 / 5000000 : ℚ), (39 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_24 : okY ((39 / 125 : ℚ), (73961 / 200000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_25 : okY ((73961 / 200000 : ℚ), (3698053 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_26 : okY ((3698053 / 10000000 : ℚ), (3 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_27 : okY ((3 / 8 : ℚ), (4213693 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_28 : okY ((4213693 / 10000000 : ℚ), (842739 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_29 : okY ((842739 / 2000000 : ℚ), (219 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_30 : okY ((219 / 500 : ℚ), (600951 / 1250000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_31 : okY ((600951 / 1250000 : ℚ), (480761 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_32 : okY ((480761 / 1000000 : ℚ), (1 / 2 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_33 : okY ((1 / 2 : ℚ), (5297969 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_34 : okY ((5297969 / 10000000 : ℚ), (5297971 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okY_35 : okY ((5297971 / 10000000 : ℚ), (281 / 500 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
