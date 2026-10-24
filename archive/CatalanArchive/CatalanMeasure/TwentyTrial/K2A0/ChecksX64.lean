module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX64 : integerGapOK AZX ((-370863 / 1000000 : ℚ),(-687 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX64 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-370863 / 1000000 : ℚ),(-687 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
