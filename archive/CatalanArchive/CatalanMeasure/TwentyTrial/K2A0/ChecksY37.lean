module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY37 : integerGapOK AZY ((281 / 500 : ℚ),(91769 / 156250 : ℚ),false)=true :=by decide +kernel
theorem bracketY37 : shiftedColumnBracketOK C Vc V AY QY MY ((281 / 500 : ℚ),(91769 / 156250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
