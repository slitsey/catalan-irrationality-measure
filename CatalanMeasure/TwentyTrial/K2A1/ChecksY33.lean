module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY33 : integerGapOK AZY ((1 / 2 : ℚ),(5464933 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY33 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 2 : ℚ),(5464933 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
