module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX50 : integerGapOK AZX ((706343 / 2500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX50 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((706343 / 2500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
