module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY40 : integerGapOK AZY ((323037 / 500000 : ℚ),(3230371 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY40 : shiftedColumnBracketOK C Vc V AY QY MY ((323037 / 500000 : ℚ),(3230371 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
