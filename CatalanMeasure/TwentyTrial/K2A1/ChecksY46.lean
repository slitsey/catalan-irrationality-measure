module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY46 : integerGapOK AZY ((900771 / 1250000 : ℚ),(720617 / 1000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY46 : shiftedColumnBracketOK C Vc V AY QY MY ((900771 / 1250000 : ℚ),(720617 / 1000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
