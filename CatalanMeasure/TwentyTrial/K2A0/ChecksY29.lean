module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY29 : integerGapOK AZY ((206021 / 500000 : ℚ),(2060211 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY29 : shiftedColumnBracketOK C Vc V AY QY MY ((206021 / 500000 : ℚ),(2060211 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
