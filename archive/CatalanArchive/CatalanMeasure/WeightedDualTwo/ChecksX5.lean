module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_90 : okX ((275327 / 1250000 : ℚ), (1101309 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_91 : okX ((1101309 / 5000000 : ℚ), (1 / 4 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_92 : okX ((1 / 4 : ℚ), (2604189 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_93 : okX ((2604189 / 10000000 : ℚ), (2604191 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_94 : okX ((2604191 / 10000000 : ℚ), (39 / 125 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_95 : okX ((39 / 125 : ℚ), (643061 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_96 : okX ((643061 / 2000000 : ℚ), (803827 / 2500000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_97 : okX ((803827 / 2500000 : ℚ), (687 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_98 : okX ((687 / 2000 : ℚ), (920261 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_99 : okX ((920261 / 2500000 : ℚ), (1840523 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_100 : okX ((1840523 / 5000000 : ℚ), (3 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_101 : okX ((3 / 8 : ℚ), (4297949 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_102 : okX ((4297949 / 10000000 : ℚ), (134311 / 312500 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_103 : okX ((134311 / 312500 : ℚ), (219 / 500 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_104 : okX ((219 / 500 : ℚ), (4768619 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_105 : okX ((4768619 / 10000000 : ℚ), (2384311 / 5000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_106 : okX ((2384311 / 5000000 : ℚ), (1 / 2 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_107 : okX ((1 / 2 : ℚ), (1069411 / 2000000 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
