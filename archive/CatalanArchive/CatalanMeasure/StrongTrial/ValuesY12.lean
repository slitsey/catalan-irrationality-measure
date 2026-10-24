module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_121 : shiftedColumnBracketOK C Vc V AY QY MY ((2237752131 / 2500000000 : ℚ),(8951008527 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_123 : shiftedColumnBracketOK C Vc V AY QY MY ((9034842063 / 10000000000 : ℚ),(4517421033 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_125 : shiftedColumnBracketOK C Vc V AY QY MY ((9114923183 / 10000000000 : ℚ),(4557461593 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_127 : shiftedColumnBracketOK C Vc V AY QY MY ((2298053909 / 2500000000 : ℚ),(9192215639 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_129 : shiftedColumnBracketOK C Vc V AY QY MY ((9265473687 / 10000000000 : ℚ),(926547369 / 1000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
