module

public import CatalanArchive.CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem okX_72 : okX ((-1 / 4 : ℚ), (-1101611 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_73 : okX ((-1101611 / 5000000 : ℚ), (-2203219 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_74 : okX ((-2203219 / 10000000 : ℚ), (-47 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_75 : okX ((-47 / 250 : ℚ), (-844917 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_76 : okX ((-844917 / 5000000 : ℚ), (-211229 / 1250000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_77 : okX ((-211229 / 1250000 : ℚ), (-313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_78 : okX ((-313 / 2000 : ℚ), (-1422699 / 10000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_79 : okX ((-1422699 / 10000000 : ℚ), (-1422697 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_80 : okX ((-1422697 / 10000000 : ℚ), (-1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_81 : okX ((-1 / 8 : ℚ), (0 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_82 : okX ((0 : ℚ), (1 / 8 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_83 : okX ((1 / 8 : ℚ), (696619 / 5000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_84 : okX ((696619 / 5000000 : ℚ), (34831 / 250000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_85 : okX ((34831 / 250000 : ℚ), (313 / 2000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_86 : okX ((313 / 2000 : ℚ), (333183 / 2000000 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_87 : okX ((333183 / 2000000 : ℚ), (1665917 / 10000000 : ℚ), true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_88 : okX ((1665917 / 10000000 : ℚ), (47 / 250 : ℚ), false) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem okX_89 : okX ((47 / 250 : ℚ), (275327 / 1250000 : ℚ), false) = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
