module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY1 : integerGapOK AZY ((183749 / 5000000 : ℚ),(147 / 4000 : ℚ),true)=true :=by decide +kernel
theorem bracketY1 : shiftedColumnBracketOK C Vc V AY QY MY ((183749 / 5000000 : ℚ),(147 / 4000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
