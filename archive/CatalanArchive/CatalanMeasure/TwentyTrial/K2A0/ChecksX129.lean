module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX129 : integerGapOK AZX ((8549921 / 10000000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX129 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((8549921 / 10000000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
