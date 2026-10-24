module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX54 : integerGapOK AZX ((3 / 8 : ℚ),(100299 / 250000 : ℚ),false)=true :=by decide +kernel
theorem bracketX54 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((3 / 8 : ℚ),(100299 / 250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
