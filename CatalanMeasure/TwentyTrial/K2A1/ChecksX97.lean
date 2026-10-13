module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX97 : integerGapOK AZX ((687 / 2000 : ℚ),(3676077 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX97 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((687 / 2000 : ℚ),(3676077 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
