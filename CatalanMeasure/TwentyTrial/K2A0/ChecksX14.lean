module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX14 : integerGapOK AZX ((-4961 / 5000 : ℚ),(-9908971 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX14 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-4961 / 5000 : ℚ),(-9908971 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
