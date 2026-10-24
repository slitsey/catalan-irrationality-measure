module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX50 : integerGapOK AZX ((-5 / 8 : ℚ),(-5940543 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX50 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-5 / 8 : ℚ),(-5940543 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
