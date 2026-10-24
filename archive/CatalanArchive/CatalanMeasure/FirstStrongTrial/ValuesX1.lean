module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_18 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1046689 / 4000000 : ℚ),(-13083611 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_20 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-19630307 / 100000000 : ℚ),(-613447 / 3125000 : ℚ),true)=true := by decide +kernel
theorem bracketX_22 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-15306479 / 100000000 : ℚ),(-3826619 / 25000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_25 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((15195543 / 100000000 : ℚ),(7597773 / 50000000 : ℚ),true)=true := by decide +kernel
theorem bracketX_27 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((985461 / 5000000 : ℚ),(19709223 / 100000000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
