module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY37 : integerGapOK AZY ((7731033 / 10000000 : ℚ),(1932759 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY37 : shiftedColumnBracketOK C Vc V AY QY MY ((7731033 / 10000000 : ℚ),(1932759 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
