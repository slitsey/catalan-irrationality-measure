module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY5 : integerGapOK AZY ((291511 / 10000000 : ℚ),(291513 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY5 : shiftedColumnBracketOK C Vc V AY QY MY ((291511 / 10000000 : ℚ),(291513 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
