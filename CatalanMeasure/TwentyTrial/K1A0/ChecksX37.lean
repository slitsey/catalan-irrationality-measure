module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX37 : integerGapOK AZX ((1424929 / 5000000 : ℚ),(142493 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX37 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1424929 / 5000000 : ℚ),(142493 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
