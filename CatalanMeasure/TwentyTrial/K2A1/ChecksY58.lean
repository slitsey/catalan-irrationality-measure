module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY58 : integerGapOK AZY ((8791993 / 10000000 : ℚ),(1758399 / 2000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY58 : shiftedColumnBracketOK C Vc V AY QY MY ((8791993 / 10000000 : ℚ),(1758399 / 2000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
