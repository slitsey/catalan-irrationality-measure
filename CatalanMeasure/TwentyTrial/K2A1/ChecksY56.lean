module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY56 : integerGapOK AZY ((423541 / 500000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY56 : shiftedColumnBracketOK C Vc V AY QY MY ((423541 / 500000 : ℚ),(7 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
