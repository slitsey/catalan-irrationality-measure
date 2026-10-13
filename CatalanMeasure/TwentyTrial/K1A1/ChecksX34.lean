module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX34 : integerGapOK AZX ((-812627 / 5000000 : ℚ),(-406313 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX34 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((-812627 / 5000000 : ℚ),(-406313 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
