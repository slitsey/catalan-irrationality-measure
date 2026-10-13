module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY3 : integerGapOK AZY ((164519 / 10000000 : ℚ),(29 / 1250 : ℚ),false)=true :=by decide +kernel
theorem bracketY3 : shiftedColumnBracketOK C Vc V AY QY MY ((164519 / 10000000 : ℚ),(29 / 1250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
