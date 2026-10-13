module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY38 : integerGapOK AZY ((91769 / 156250 : ℚ),(2936609 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY38 : shiftedColumnBracketOK C Vc V AY QY MY ((91769 / 156250 : ℚ),(2936609 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
