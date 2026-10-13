module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY49 : integerGapOK AZY ((3 / 4 : ℚ),(7800867 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY49 : shiftedColumnBracketOK C Vc V AY QY MY ((3 / 4 : ℚ),(7800867 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
