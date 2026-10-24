module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX21 : integerGapOK AZX ((-9670259 / 10000000 : ℚ),(-9670257 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX21 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9670259 / 10000000 : ℚ),(-9670257 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
