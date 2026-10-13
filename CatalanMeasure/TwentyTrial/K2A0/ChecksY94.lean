module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY94 : integerGapOK AZY ((9998789 / 10000000 : ℚ),(1 : ℚ),false)=true :=by decide +kernel
theorem bracketY94 : shiftedColumnBracketOK C Vc V AY QY MY ((9998789 / 10000000 : ℚ),(1 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
