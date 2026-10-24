module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX35 : integerGapOK AZX ((-1687 / 2000 : ℚ),(-1035441 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketX35 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1687 / 2000 : ℚ),(-1035441 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
