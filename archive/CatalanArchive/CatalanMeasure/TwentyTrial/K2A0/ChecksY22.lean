module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY22 : integerGapOK AZY ((1 / 4 : ℚ),(1468213 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY22 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 4 : ℚ),(1468213 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
