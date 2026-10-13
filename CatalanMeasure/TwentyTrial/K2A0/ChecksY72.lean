module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY72 : integerGapOK AZY ((2433017 / 2500000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
theorem bracketY72 : shiftedColumnBracketOK C Vc V AY QY MY ((2433017 / 2500000 : ℚ),(1221 / 1250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
