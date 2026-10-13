module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX59 : integerGapOK AZX ((331537 / 500000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketX59 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((331537 / 500000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
