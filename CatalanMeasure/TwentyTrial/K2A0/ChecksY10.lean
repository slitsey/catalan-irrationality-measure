module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY10 : integerGapOK AZY ((31 / 500 : ℚ),(110799 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketY10 : shiftedColumnBracketOK C Vc V AY QY MY ((31 / 500 : ℚ),(110799 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
