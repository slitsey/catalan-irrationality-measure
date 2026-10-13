module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX24 : integerGapOK AZX ((-1184033 / 1250000 : ℚ),(-4736131 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX24 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1184033 / 1250000 : ℚ),(-4736131 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
