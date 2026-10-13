module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY13 : integerGapOK AZY ((1587473 / 10000000 : ℚ),(63499 / 400000 : ℚ),true)=true :=by decide +kernel
theorem bracketY13 : shiftedColumnBracketOK C Vc V AY QY MY ((1587473 / 10000000 : ℚ),(63499 / 400000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
