module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY33 : integerGapOK AZY ((1185217 / 2500000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
theorem bracketY33 : shiftedColumnBracketOK C Vc V AY QY MY ((1185217 / 2500000 : ℚ),(1 / 2 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
