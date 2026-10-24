module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX43 : integerGapOK AZX ((-935359 / 1250000 : ℚ),(-719 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketX43 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-935359 / 1250000 : ℚ),(-719 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
