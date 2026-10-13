module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY52 : integerGapOK AZY ((4044993 / 5000000 : ℚ),(2022497 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY52 : shiftedColumnBracketOK C Vc V AY QY MY ((4044993 / 5000000 : ℚ),(2022497 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
