module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY48 : integerGapOK AZY ((45987 / 62500 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY48 : shiftedColumnBracketOK C Vc V AY QY MY ((45987 / 62500 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
