module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX70 : integerGapOK AZX ((-2714731 / 10000000 : ℚ),(-1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketX70 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2714731 / 10000000 : ℚ),(-1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
