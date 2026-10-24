module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX109 : integerGapOK AZX ((281 / 500 : ℚ),(2937679 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX109 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((281 / 500 : ℚ),(2937679 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
