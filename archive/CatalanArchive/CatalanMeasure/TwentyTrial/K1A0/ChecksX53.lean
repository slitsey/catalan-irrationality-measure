module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX53 : integerGapOK AZX ((2847053 / 5000000 : ℚ),(1187 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketX53 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((2847053 / 5000000 : ℚ),(1187 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
