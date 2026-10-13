module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY4 : integerGapOK AZY ((29 / 1250 : ℚ),(291511 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY4 : shiftedColumnBracketOK C Vc V AY QY MY ((29 / 1250 : ℚ),(291511 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
