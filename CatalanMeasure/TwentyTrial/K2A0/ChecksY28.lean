module
public import CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY28 : integerGapOK AZY ((3 / 8 : ℚ),(206021 / 500000 : ℚ),false)=true :=by decide +kernel
theorem bracketY28 : shiftedColumnBracketOK C Vc V AY QY MY ((3 / 8 : ℚ),(206021 / 500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
