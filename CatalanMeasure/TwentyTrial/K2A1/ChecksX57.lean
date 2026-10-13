module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX57 : integerGapOK AZX ((-1255477 / 2500000 : ℚ),(-2510953 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX57 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1255477 / 2500000 : ℚ),(-2510953 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
