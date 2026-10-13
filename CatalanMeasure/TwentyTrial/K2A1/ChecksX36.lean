module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX36 : integerGapOK AZX ((-8458511 / 10000000 : ℚ),(-2114627 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX36 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-8458511 / 10000000 : ℚ),(-2114627 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
