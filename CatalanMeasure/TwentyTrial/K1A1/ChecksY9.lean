module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY9 : integerGapOK AZY ((47 / 250 : ℚ),(550041 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketY9 : shiftedColumnBracketOK C Vc V AY QY MY ((47 / 250 : ℚ),(550041 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
