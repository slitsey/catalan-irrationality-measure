module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX42 : integerGapOK AZX ((-1908677 / 2500000 : ℚ),(-3817353 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX42 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-1908677 / 2500000 : ℚ),(-3817353 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
