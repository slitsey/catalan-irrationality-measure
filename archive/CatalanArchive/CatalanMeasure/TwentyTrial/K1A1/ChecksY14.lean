module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY14 : integerGapOK AZY ((297569 / 1000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY14 : shiftedColumnBracketOK C Vc V AY QY MY ((297569 / 1000000 : ℚ),(39 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
