module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX38 : integerGapOK AZX ((-203 / 250 : ℚ),(-7893251 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX38 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-203 / 250 : ℚ),(-7893251 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
