module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY13 : integerGapOK AZY ((1 / 8 : ℚ),(1364207 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY13 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 8 : ℚ),(1364207 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
