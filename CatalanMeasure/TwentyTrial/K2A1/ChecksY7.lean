module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY7 : integerGapOK AZY ((365277 / 5000000 : ℚ),(182639 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY7 : shiftedColumnBracketOK C Vc V AY QY MY ((365277 / 5000000 : ℚ),(182639 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
