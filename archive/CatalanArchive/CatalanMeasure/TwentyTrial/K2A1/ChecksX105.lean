module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX105 : integerGapOK AZX ((598753 / 1250000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
theorem bracketX105 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((598753 / 1250000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
