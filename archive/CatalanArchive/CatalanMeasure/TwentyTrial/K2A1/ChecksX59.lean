module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX59 : integerGapOK AZX ((-1 / 2 : ℚ),(-35911 / 80000 : ℚ),false)=true :=by decide +kernel
theorem bracketX59 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1 / 2 : ℚ),(-35911 / 80000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
