module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_1 : shiftedColumnBracketOK C Vc V AY QY MY ((126570803 / 10000000000 : ℚ),(63285403 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_3 : shiftedColumnBracketOK C Vc V AY QY MY ((196575351 / 10000000000 : ℚ),(98287677 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_5 : shiftedColumnBracketOK C Vc V AY QY MY ((325447171 / 10000000000 : ℚ),(162723587 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_7 : shiftedColumnBracketOK C Vc V AY QY MY ((440073617 / 10000000000 : ℚ),(22003681 / 500000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_9 : shiftedColumnBracketOK C Vc V AY QY MY ((149246527 / 2500000000 : ℚ),(596986111 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
