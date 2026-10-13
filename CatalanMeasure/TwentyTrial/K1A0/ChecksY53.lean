module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY53 : integerGapOK AZY ((9456699 / 10000000 : ℚ),(1907 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketY53 : shiftedColumnBracketOK C Vc V AY QY MY ((9456699 / 10000000 : ℚ),(1907 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
