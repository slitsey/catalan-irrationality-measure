module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX70 : integerGapOK AZX ((832029 / 1250000 : ℚ),(1331247 / 2000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX70 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((832029 / 1250000 : ℚ),(1331247 / 2000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
