module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY1 : integerGapOK AZY ((31 / 2000 : ℚ),(164517 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY1 : shiftedColumnBracketOK C Vc V AY QY MY ((31 / 2000 : ℚ),(164517 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
