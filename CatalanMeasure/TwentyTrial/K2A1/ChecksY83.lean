module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY83 : integerGapOK AZY ((9980547 / 10000000 : ℚ),(9980549 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY83 : shiftedColumnBracketOK C Vc V AY QY MY ((9980547 / 10000000 : ℚ),(9980549 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
