module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY89 : integerGapOK AZY ((99951 / 100000 : ℚ),(9997291 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY89 : shiftedColumnBracketOK C Vc V AY QY MY ((99951 / 100000 : ℚ),(9997291 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
