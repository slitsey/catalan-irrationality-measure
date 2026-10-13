module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY7 : integerGapOK AZY ((751193 / 5000000 : ℚ),(1502389 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY7 : shiftedColumnBracketOK C Vc V AY QY MY ((751193 / 5000000 : ℚ),(1502389 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
