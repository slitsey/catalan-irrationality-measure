module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY27 : integerGapOK AZY ((281 / 500 : ℚ),(1228099 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY27 : shiftedColumnBracketOK C Vc V AY QY MY ((281 / 500 : ℚ),(1228099 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
