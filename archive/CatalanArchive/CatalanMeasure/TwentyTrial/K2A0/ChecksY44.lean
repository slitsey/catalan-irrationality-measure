module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY44 : integerGapOK AZY ((431 / 625 : ℚ),(3448001 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY44 : shiftedColumnBracketOK C Vc V AY QY MY ((431 / 625 : ℚ),(3448001 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
