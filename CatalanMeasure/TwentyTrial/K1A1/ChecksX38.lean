module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX38 : integerGapOK AZX ((-248507 / 2000000 : ℚ),(0 : ℚ),false)=true :=by decide +kernel
theorem bracketX38 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-248507 / 2000000 : ℚ),(0 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
