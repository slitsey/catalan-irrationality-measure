module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY30 : integerGapOK AZY ((2060211 / 5000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY30 : shiftedColumnBracketOK C Vc V AY QY MY ((2060211 / 5000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
