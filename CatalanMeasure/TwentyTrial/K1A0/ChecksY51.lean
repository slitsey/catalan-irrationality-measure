module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY51 : integerGapOK AZY ((469 / 500 : ℚ),(9456697 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY51 : shiftedColumnBracketOK C Vc V AY QY MY ((469 / 500 : ℚ),(9456697 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
