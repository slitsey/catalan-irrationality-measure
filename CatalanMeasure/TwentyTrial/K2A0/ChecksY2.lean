module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY2 : integerGapOK AZY ((164517 / 10000000 : ℚ),(164519 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY2 : shiftedColumnBracketOK C Vc V AY QY MY ((164517 / 10000000 : ℚ),(164519 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
