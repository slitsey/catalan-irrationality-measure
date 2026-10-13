module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY71 : integerGapOK AZY ((9696453 / 10000000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
theorem bracketY71 : shiftedColumnBracketOK C Vc V AY QY MY ((9696453 / 10000000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
