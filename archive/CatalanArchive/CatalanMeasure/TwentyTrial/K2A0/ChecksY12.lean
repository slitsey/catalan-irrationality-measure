module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY12 : integerGapOK AZY ((443197 / 5000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
theorem bracketY12 : shiftedColumnBracketOK C Vc V AY QY MY ((443197 / 5000000 : ℚ),(1 / 8 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
