module
public import CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY10 : integerGapOK AZY ((550041 / 2500000 : ℚ),(1100083 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY10 : shiftedColumnBracketOK C Vc V AY QY MY ((550041 / 2500000 : ℚ),(1100083 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
