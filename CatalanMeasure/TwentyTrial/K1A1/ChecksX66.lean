module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX66 : integerGapOK AZX ((1187 / 2000 : ℚ),(248171 / 400000 : ℚ),false)=true :=by decide +kernel
theorem bracketX66 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1187 / 2000 : ℚ),(248171 / 400000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
