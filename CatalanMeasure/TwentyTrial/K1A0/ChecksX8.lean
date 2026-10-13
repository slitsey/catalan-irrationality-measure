module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX8 : integerGapOK AZX ((-944589 / 2500000 : ℚ),(-3778353 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX8 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-944589 / 2500000 : ℚ),(-3778353 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
