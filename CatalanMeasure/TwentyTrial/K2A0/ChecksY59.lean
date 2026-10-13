module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY59 : integerGapOK AZY ((2221123 / 2500000 : ℚ),(4442247 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY59 : shiftedColumnBracketOK C Vc V AY QY MY ((2221123 / 2500000 : ℚ),(4442247 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
