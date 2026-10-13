module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX58 : integerGapOK AZX ((-2510953 / 5000000 : ℚ),(-1 / 2 : ℚ),false)=true :=by decide +kernel
theorem bracketX58 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2510953 / 5000000 : ℚ),(-1 / 2 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
