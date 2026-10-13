module
public import CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY38 : integerGapOK AZY ((3856477 / 5000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketY38 : shiftedColumnBracketOK C Vc V AY QY MY ((3856477 / 5000000 : ℚ),(203 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
