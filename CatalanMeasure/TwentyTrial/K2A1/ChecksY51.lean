module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY51 : integerGapOK AZY ((781 / 1000 : ℚ),(4044993 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY51 : shiftedColumnBracketOK C Vc V AY QY MY ((781 / 1000 : ℚ),(4044993 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
