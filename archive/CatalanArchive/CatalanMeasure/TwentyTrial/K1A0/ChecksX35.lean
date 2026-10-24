module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX35 : integerGapOK AZX ((290673 / 1250000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketX35 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((290673 / 1250000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
