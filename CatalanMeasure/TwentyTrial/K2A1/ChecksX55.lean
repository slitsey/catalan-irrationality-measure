module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX55 : integerGapOK AZX ((-5606123 / 10000000 : ℚ),(-531 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketX55 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-5606123 / 10000000 : ℚ),(-531 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
