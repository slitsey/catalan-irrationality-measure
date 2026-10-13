module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY65 : integerGapOK AZY ((4695493 / 5000000 : ℚ),(2347747 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY65 : shiftedColumnBracketOK C Vc V AY QY MY ((4695493 / 5000000 : ℚ),(2347747 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
