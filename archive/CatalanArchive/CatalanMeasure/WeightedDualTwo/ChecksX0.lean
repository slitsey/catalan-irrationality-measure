module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_0 : okX ((-1 : ℚ), (-9999813 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_1 : okX ((-9999813 / 10000000 : ℚ), (-9999811 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_2 : okX ((-9999811 / 10000000 : ℚ), (-499939 / 500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_3 : okX ((-499939 / 500000 : ℚ), (-9997591 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_4 : okX ((-9997591 / 10000000 : ℚ), (-9997589 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_5 : okX ((-9997589 / 10000000 : ℚ), (-199951 / 200000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_6 : okX ((-199951 / 200000 : ℚ), (-99951 / 100000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_7 : okX ((-99951 / 100000 : ℚ), (-49951 / 50000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_8 : okX ((-49951 / 50000 : ℚ), (-9989003 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_9 : okX ((-9989003 / 10000000 : ℚ), (-9989001 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_10 : okX ((-9989001 / 10000000 : ℚ), (-19961 / 20000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_11 : okX ((-19961 / 20000 : ℚ), (-9961 / 10000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_12 : okX ((-9961 / 10000 : ℚ), (-9956577 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_13 : okX ((-9956577 / 10000000 : ℚ), (-4978287 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_14 : okX ((-4978287 / 5000000 : ℚ), (-4961 / 5000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_15 : okX ((-4961 / 5000 : ℚ), (-2475223 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_16 : okX ((-2475223 / 2500000 : ℚ), (-990089 / 1000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_17 : okX ((-990089 / 1000000 : ℚ), (-1969 / 2000 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
