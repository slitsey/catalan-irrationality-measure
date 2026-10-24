module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY21 : integerGapOK AZY ((219 / 500 : ℚ),(4854623 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY21 : shiftedColumnBracketOK C Vc V AY QY MY ((219 / 500 : ℚ),(4854623 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
