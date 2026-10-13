module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY15 : integerGapOK AZY ((39 / 125 : ℚ),(720701 / 2000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY15 : shiftedColumnBracketOK C Vc V AY QY MY ((39 / 125 : ℚ),(720701 / 2000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
