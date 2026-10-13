module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY2 : integerGapOK AZY ((147 / 4000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY2 : shiftedColumnBracketOK C Vc V AY QY MY ((147 / 4000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
