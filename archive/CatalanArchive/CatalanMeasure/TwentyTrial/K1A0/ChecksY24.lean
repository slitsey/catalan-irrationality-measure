module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY24 : integerGapOK AZY ((1 / 2 : ℚ),(5531143 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY24 : shiftedColumnBracketOK C Vc V AY QY MY ((1 / 2 : ℚ),(5531143 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
