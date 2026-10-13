module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY42 : integerGapOK AZY ((3191821 / 5000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY42 : shiftedColumnBracketOK C Vc V AY QY MY ((3191821 / 5000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
