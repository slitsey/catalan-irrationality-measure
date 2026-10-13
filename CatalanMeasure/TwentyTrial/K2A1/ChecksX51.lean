module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX51 : integerGapOK AZX ((-6137591 / 10000000 : ℚ),(-6137589 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX51 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-6137591 / 10000000 : ℚ),(-6137589 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
