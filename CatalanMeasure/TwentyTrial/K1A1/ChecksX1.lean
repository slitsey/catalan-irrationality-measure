module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX1 : integerGapOK AZX ((-399993 / 400000 : ℚ),(-9999823 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX1 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-399993 / 400000 : ℚ),(-9999823 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
