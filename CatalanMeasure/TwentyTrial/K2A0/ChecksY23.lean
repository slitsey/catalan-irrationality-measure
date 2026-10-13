module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY23 : integerGapOK AZY ((1468213 / 5000000 : ℚ),(734107 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY23 : shiftedColumnBracketOK C Vc V AY QY MY ((1468213 / 5000000 : ℚ),(734107 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
