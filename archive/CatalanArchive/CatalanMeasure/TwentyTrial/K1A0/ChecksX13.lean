module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX13 : integerGapOK AZX ((-39 / 125 : ℚ),(-2714961 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX13 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-39 / 125 : ℚ),(-2714961 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
