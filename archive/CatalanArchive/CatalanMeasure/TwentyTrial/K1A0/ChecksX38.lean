module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX38 : integerGapOK AZX ((142493 / 500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX38 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((142493 / 500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
