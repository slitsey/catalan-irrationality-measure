module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY2 : integerGapOK AZY ((238697 / 10000000 : ℚ),(31 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY2 : shiftedColumnBracketOK C Vc V AY QY MY ((238697 / 10000000 : ℚ),(31 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
