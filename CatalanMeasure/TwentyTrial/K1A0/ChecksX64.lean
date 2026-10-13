module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX64 : integerGapOK AZX ((7292917 / 10000000 : ℚ),(7292919 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX64 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((7292917 / 10000000 : ℚ),(7292919 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
