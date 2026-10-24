module
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_1 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999997449 / 10000000000 : ℚ),(-4999998723 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_3 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999971017 / 10000000000 : ℚ),(-4999985507 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_5 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999770729 / 10000000000 : ℚ),(-4999885363 / 5000000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_7 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999033047 / 10000000000 : ℚ),(-2499758261 / 2500000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_9 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-124959053 / 125000000 : ℚ),(-9996724237 / 10000000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.StrongTrial
