module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY48 : integerGapOK AZY ((1813 / 2000 : ℚ),(1841203 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY48 : shiftedColumnBracketOK C Vc V AY QY MY ((1813 / 2000 : ℚ),(1841203 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
