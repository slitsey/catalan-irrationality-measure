module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY35 : integerGapOK AZY ((1092987 / 2000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY35 : shiftedColumnBracketOK C Vc V AY QY MY ((1092987 / 2000000 : ℚ),(281 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
