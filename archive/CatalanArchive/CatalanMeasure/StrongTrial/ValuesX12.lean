module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_121 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1166881529 / 2500000000 : ℚ),(-4667526113 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_123 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4496501261 / 10000000000 : ℚ),(-2248250629 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_125 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2164245607 / 5000000000 : ℚ),(-4328491211 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_127 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4153778189 / 10000000000 : ℚ),(-2076889093 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_129 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-199158149 / 500000000 : ℚ),(-3983162977 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
