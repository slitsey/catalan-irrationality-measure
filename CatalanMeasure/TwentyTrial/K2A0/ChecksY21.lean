module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY21 : integerGapOK AZY ((2409567 / 10000000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY21 : shiftedColumnBracketOK C Vc V AY QY MY ((2409567 / 10000000 : ℚ),(1 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
