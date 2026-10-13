module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY49 : integerGapOK AZY ((1841203 / 2000000 : ℚ),(9206017 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY49 : shiftedColumnBracketOK C Vc V AY QY MY ((1841203 / 2000000 : ℚ),(9206017 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
