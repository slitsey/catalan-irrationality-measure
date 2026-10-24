module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX11 : integerGapOK AZX ((-9961 / 10000 : ℚ),(-995931 / 1000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX11 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9961 / 10000 : ℚ),(-995931 / 1000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
