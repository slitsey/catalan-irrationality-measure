module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX0 : integerGapOK AZX ((-1 : ℚ),(-9999959 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX0 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1 : ℚ),(-9999959 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
