module
public import CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_202 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((446469531 / 1000000000 : ℚ),(4464695313 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_204 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4636175893 / 10000000000 : ℚ),(579521987 / 1250000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_206 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4801368157 / 10000000000 : ℚ),(30008551 / 62500000 : ℚ),true)=true := by decide +kernel
theorem bracketX_208 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((4969121617 / 10000000000 : ℚ),(248456081 / 500000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_210 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5131264887 / 10000000000 : ℚ),(513126489 / 1000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
