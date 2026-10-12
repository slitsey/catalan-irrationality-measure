module

public import CatalanMeasure.WeightedDualTwo.Data

@[expose] public section

namespace CatalanMeasure.WeightedDualTwo

open CatalanMeasure.Cert

set_option maxRecDepth 1000000 in
theorem hAQX : fracSum (rowFracs Pc Vc P V) = (AX, QX) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hAQY : fracSum (modColFracs Vc V) = (AY, QY) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchainX : rowCheck P V AX planX = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchainY : colCheck V AY planY = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hendX : rowEndOK Pc Vc P V MX = true := by decide +kernel

end CatalanMeasure.WeightedDualTwo
