module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY29 : integerGapOK AZY ((2172121 / 5000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY29 : shiftedColumnBracketOK C Vc V AY QY MY ((2172121 / 5000000 : ℚ),(219 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
