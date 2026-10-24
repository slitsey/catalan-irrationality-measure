module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX64 : integerGapOK AZX ((-154401 / 400000 : ℚ),(-3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX64 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-154401 / 400000 : ℚ),(-3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
