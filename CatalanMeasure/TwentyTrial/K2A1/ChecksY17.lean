module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY17 : integerGapOK AZY ((1020403 / 5000000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY17 : shiftedColumnBracketOK C Vc V AY QY MY ((1020403 / 5000000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
