module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY66 : integerGapOK AZY ((469 / 500 : ℚ),(9521313 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY66 : shiftedColumnBracketOK C Vc V AY QY MY ((469 / 500 : ℚ),(9521313 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
