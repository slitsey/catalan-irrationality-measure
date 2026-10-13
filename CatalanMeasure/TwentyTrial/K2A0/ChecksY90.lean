module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY90 : integerGapOK AZY ((9997291 / 10000000 : ℚ),(9997293 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY90 : shiftedColumnBracketOK C Vc V AY QY MY ((9997291 / 10000000 : ℚ),(9997293 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
