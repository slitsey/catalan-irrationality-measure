module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY14 : integerGapOK AZY ((1364207 / 10000000 : ℚ),(1364209 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY14 : shiftedColumnBracketOK C Vc V AY QY MY ((1364207 / 10000000 : ℚ),(1364209 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
