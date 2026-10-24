module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY25 : integerGapOK AZY ((5531143 / 10000000 : ℚ),(1106229 / 2000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY25 : shiftedColumnBracketOK C Vc V AY QY MY ((5531143 / 10000000 : ℚ),(1106229 / 2000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
