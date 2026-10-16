module
public import CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_1 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-49999441 / 50000000 : ℚ),(-99998879 / 100000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_10 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-45596901 / 100000000 : ℚ),(-22798449 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_12 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-41823973 / 100000000 : ℚ),(-4182397 / 10000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_14 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-36642733 / 100000000 : ℚ),(-3664273 / 10000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_16 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-3909823 / 12500000 : ℚ),(-31278581 / 100000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
