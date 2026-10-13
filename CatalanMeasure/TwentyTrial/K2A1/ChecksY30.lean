module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY30 : integerGapOK AZY ((219 / 500 : ℚ),(4963237 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY30 : shiftedColumnBracketOK C Vc V AY QY MY ((219 / 500 : ℚ),(4963237 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
