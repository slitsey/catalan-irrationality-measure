module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX43 : integerGapOK AZX ((1659459 / 10000000 : ℚ),(829731 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX43 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1659459 / 10000000 : ℚ),(829731 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
