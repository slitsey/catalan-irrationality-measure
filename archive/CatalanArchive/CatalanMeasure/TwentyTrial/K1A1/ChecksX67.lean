module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX67 : integerGapOK AZX ((248171 / 400000 : ℚ),(6204277 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX67 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((248171 / 400000 : ℚ),(6204277 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
