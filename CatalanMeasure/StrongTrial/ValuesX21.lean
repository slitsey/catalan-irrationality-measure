module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_212 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1323742841 / 2500000000 : ℚ),(5294971367 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_214 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5454215817 / 10000000000 : ℚ),(272710791 / 500000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_216 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5614166497 / 10000000000 : ℚ),(11228333 / 20000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_218 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5769542687 / 10000000000 : ℚ),(576954269 / 1000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_220 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5925321003 / 10000000000 : ℚ),(2962660503 / 5000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
