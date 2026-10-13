module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY5 : integerGapOK AZY ((24323 / 625000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY5 : shiftedColumnBracketOK C Vc V AY QY MY ((24323 / 625000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
