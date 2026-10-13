module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY26 : integerGapOK AZY ((1106229 / 2000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY26 : shiftedColumnBracketOK C Vc V AY QY MY ((1106229 / 2000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
