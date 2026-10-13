module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX51 : integerGapOK AZX ((281 / 500 : ℚ),(711763 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketX51 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((281 / 500 : ℚ),(711763 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
