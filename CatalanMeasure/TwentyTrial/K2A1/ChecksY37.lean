module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY37 : integerGapOK AZY ((754893 / 1250000 : ℚ),(3019573 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY37 : shiftedColumnBracketOK C Vc V AY QY MY ((754893 / 1250000 : ℚ),(3019573 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
