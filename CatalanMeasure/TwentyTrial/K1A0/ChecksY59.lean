module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY59 : integerGapOK AZY ((1226349 / 1250000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketY59 : shiftedColumnBracketOK C Vc V AY QY MY ((1226349 / 1250000 : ℚ),(1969 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
