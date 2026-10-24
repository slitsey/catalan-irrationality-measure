module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX1 : integerGapOK AZX ((-9999959 / 10000000 : ℚ),(-9999957 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX1 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9999959 / 10000000 : ℚ),(-9999957 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
