module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY64 : integerGapOK AZY ((469 / 500 : ℚ),(4695493 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY64 : shiftedColumnBracketOK C Vc V AY QY MY ((469 / 500 : ℚ),(4695493 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
