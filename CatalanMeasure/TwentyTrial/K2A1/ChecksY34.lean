module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY34 : integerGapOK AZY ((5464933 / 10000000 : ℚ),(1092987 / 2000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY34 : shiftedColumnBracketOK C Vc V AY QY MY ((5464933 / 10000000 : ℚ),(1092987 / 2000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
