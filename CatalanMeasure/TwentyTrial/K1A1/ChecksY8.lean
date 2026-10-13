module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY8 : integerGapOK AZY ((796137 / 5000000 : ℚ),(47 / 250 : ℚ),false)=true :=by decide +kernel
theorem bracketY8 : shiftedColumnBracketOK C Vc V AY QY MY ((796137 / 5000000 : ℚ),(47 / 250 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
