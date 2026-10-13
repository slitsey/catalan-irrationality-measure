module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX14 : integerGapOK AZX ((-2714961 / 10000000 : ℚ),(-2714959 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX14 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-2714961 / 10000000 : ℚ),(-2714959 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
