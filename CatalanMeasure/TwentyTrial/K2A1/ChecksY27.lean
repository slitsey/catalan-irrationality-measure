module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY27 : integerGapOK AZY ((813 / 2000 : ℚ),(54303 / 125000 : ℚ),false)=true :=by decide +kernel
theorem bracketY27 : shiftedColumnBracketOK C Vc V AY QY MY ((813 / 2000 : ℚ),(54303 / 125000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
