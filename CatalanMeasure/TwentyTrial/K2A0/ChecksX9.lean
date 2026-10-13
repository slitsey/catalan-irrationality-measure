module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX9 : integerGapOK AZX ((-499469 / 500000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
theorem bracketX9 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-499469 / 500000 : ℚ),(-19961 / 20000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
