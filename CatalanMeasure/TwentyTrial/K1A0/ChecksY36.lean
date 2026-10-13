module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY36 : integerGapOK AZY ((3 / 4 : ℚ),(964119 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketY36 : shiftedColumnBracketOK C Vc V AY QY MY ((3 / 4 : ℚ),(964119 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
