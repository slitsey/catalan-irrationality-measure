module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX91 : integerGapOK AZX ((1 / 4 : ℚ),(520893 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX91 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1 / 4 : ℚ),(520893 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
