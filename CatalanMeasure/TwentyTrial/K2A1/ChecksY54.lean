module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY54 : integerGapOK AZY ((203 / 250 : ℚ),(4235409 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY54 : shiftedColumnBracketOK C Vc V AY QY MY ((203 / 250 : ℚ),(4235409 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
