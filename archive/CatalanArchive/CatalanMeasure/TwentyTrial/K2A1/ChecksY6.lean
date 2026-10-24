module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY6 : integerGapOK AZY ((31 / 500 : ℚ),(365277 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY6 : shiftedColumnBracketOK C Vc V AY QY MY ((31 / 500 : ℚ),(365277 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
