module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketY_111 : shiftedColumnBracketOK C Vc V AY QY MY ((4241803979 / 5000000000 : ℚ),(8483607961 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_113 : shiftedColumnBracketOK C Vc V AY QY MY ((343342717 / 400000000 : ℚ),(1072945991 / 1250000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_115 : shiftedColumnBracketOK C Vc V AY QY MY ((8680377557 / 10000000000 : ℚ),(217009439 / 250000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_117 : shiftedColumnBracketOK C Vc V AY QY MY ((8774062079 / 10000000000 : ℚ),(4387031041 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketY_119 : shiftedColumnBracketOK C Vc V AY QY MY ((34625909 / 39062500 : ℚ),(8864232707 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
