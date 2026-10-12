module

public import CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_144 : okX ((9483821 / 10000000 : ℚ), (9483823 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_145 : okX ((9483823 / 10000000 : ℚ), (1907 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_146 : okX ((1907 / 2000 : ℚ), (2415273 / 2500000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_147 : okX ((2415273 / 2500000 : ℚ), (1932219 / 2000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_148 : okX ((1932219 / 2000000 : ℚ), (969 / 1000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_149 : okX ((969 / 1000 : ℚ), (9761617 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_150 : okX ((9761617 / 10000000 : ℚ), (9761619 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_151 : okX ((9761619 / 10000000 : ℚ), (1969 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_152 : okX ((1969 / 2000 : ℚ), (9863991 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_153 : okX ((9863991 / 10000000 : ℚ), (9863993 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_154 : okX ((9863993 / 10000000 : ℚ), (19767 / 20000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_155 : okX ((19767 / 20000 : ℚ), (4953413 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_156 : okX ((4953413 / 5000000 : ℚ), (9906829 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_157 : okX ((9906829 / 10000000 : ℚ), (4961 / 5000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_158 : okX ((4961 / 5000 : ℚ), (1 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
