module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY50 : integerGapOK AZY ((9206017 / 10000000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY50 : shiftedColumnBracketOK C Vc V AY QY MY ((9206017 / 10000000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
