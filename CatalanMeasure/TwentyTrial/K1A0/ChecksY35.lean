module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY35 : integerGapOK AZY ((3596009 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
theorem bracketY35 : shiftedColumnBracketOK C Vc V AY QY MY ((3596009 / 5000000 : ℚ),(3 / 4 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
