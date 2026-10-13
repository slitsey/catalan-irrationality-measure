module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY36 : integerGapOK AZY ((5294281 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY36 : shiftedColumnBracketOK C Vc V AY QY MY ((5294281 / 10000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
