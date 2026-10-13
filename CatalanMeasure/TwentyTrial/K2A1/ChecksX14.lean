module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX14 : integerGapOK AZX ((-9961 / 10000 : ℚ),(-155211 / 156250 : ℚ),false)=true :=by decide +kernel
theorem bracketX14 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-9961 / 10000 : ℚ),(-155211 / 156250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
