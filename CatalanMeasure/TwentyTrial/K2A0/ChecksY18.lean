module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY18 : integerGapOK AZY ((907423 / 5000000 : ℚ),(47 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketY18 : shiftedColumnBracketOK C Vc V AY QY MY ((907423 / 5000000 : ℚ),(47 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
