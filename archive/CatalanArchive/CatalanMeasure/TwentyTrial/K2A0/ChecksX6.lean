module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX6 : integerGapOK AZX ((-99951 / 100000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
theorem bracketX6 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-99951 / 100000 : ℚ),(-49951 / 50000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
