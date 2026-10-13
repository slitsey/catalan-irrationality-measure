module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX35 : integerGapOK AZX ((-7 / 8 : ℚ),(-8458511 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX35 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-7 / 8 : ℚ),(-8458511 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
