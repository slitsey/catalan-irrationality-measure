module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX74 : integerGapOK AZX ((-47 / 250 : ℚ),(-1735449 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX74 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-47 / 250 : ℚ),(-1735449 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
