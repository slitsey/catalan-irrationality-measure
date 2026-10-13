module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX22 : integerGapOK AZX ((-9741569 / 10000000 : ℚ),(-969 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketX22 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9741569 / 10000000 : ℚ),(-969 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
