module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY70 : integerGapOK AZY ((969 / 1000 : ℚ),(1946413 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY70 : shiftedColumnBracketOK C Vc V AY QY MY ((969 / 1000 : ℚ),(1946413 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
