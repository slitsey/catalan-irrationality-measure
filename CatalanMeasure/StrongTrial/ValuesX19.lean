module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_192 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((900716947 / 2500000000 : ℚ),(3602867791 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_194 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((471806841 / 1250000000 : ℚ),(3774454731 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_196 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((24700069 / 62500000 : ℚ),(3952011043 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_198 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4122119997 / 10000000000 : ℚ),(103053 / 250000 : ℚ),true)=true := by decide +kernel
theorem bracketX_200 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((429655581 / 1000000000 : ℚ),(4296555813 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
