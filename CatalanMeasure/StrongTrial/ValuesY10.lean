module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_101 : shiftedColumnBracketOK C Vc V AY QY MY ((7938085273 / 10000000000 : ℚ),(1984521319 / 2500000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_103 : shiftedColumnBracketOK C Vc V AY QY MY ((805279851 / 1000000000 : ℚ),(8052798513 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_105 : shiftedColumnBracketOK C Vc V AY QY MY ((163302179 / 200000000 : ℚ),(8165108953 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_107 : shiftedColumnBracketOK C Vc V AY QY MY ((129285443 / 156250000 : ℚ),(1654853671 / 2000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_109 : shiftedColumnBracketOK C Vc V AY QY MY ((209518973 / 250000000 : ℚ),(8380758923 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
