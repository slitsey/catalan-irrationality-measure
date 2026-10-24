module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY24 : integerGapOK AZY ((734107 / 2500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY24 : shiftedColumnBracketOK C Vc V AY QY MY ((734107 / 2500000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
