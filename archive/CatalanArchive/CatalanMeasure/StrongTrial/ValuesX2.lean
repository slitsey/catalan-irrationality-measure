module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_21 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2480138423 / 2500000000 : ℚ),(-9920553689 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_23 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9895594619 / 10000000000 : ℚ),(-1236949327 / 1250000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_25 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9866295249 / 10000000000 : ℚ),(-4933147623 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_27 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4916939423 / 5000000000 : ℚ),(-9833878843 / 10000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_29 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9797070003 / 10000000000 : ℚ),(-979707 / 1000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
