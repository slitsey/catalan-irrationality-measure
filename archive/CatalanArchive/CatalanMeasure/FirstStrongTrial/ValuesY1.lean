module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_11 : shiftedColumnBracketOK C Vc V AY QY MY ((17742161 / 50000000 : ℚ),(1419373 / 4000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_13 : shiftedColumnBracketOK C Vc V AY QY MY ((21332863 / 50000000 : ℚ),(42665729 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_15 : shiftedColumnBracketOK C Vc V AY QY MY ((9766901 / 20000000 : ℚ),(12208627 / 25000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_17 : shiftedColumnBracketOK C Vc V AY QY MY ((55442497 / 100000000 : ℚ),(22177 / 40000 : ℚ),true)=true := by decide +kernel
theorem bracketY_19 : shiftedColumnBracketOK C Vc V AY QY MY ((30583451 / 50000000 : ℚ),(12233381 / 20000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
