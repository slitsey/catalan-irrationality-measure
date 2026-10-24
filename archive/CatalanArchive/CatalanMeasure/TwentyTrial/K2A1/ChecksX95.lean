module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX95 : integerGapOK AZX ((3181127 / 10000000 : ℚ),(3181129 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX95 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3181127 / 10000000 : ℚ),(3181129 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
