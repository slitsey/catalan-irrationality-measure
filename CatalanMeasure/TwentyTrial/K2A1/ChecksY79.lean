module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY79 : integerGapOK AZY ((397933 / 400000 : ℚ),(1243541 / 1250000 : ℚ),true)=true :=by decide +kernel
theorem bracketY79 : shiftedColumnBracketOK C Vc V AY QY MY ((397933 / 400000 : ℚ),(1243541 / 1250000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
