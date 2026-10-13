module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX53 : integerGapOK AZX ((172489 / 500000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketX53 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((172489 / 500000 : ℚ),(3 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
