module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY50 : integerGapOK AZY ((7800867 / 10000000 : ℚ),(7800869 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY50 : shiftedColumnBracketOK C Vc V AY QY MY ((7800867 / 10000000 : ℚ),(7800869 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
