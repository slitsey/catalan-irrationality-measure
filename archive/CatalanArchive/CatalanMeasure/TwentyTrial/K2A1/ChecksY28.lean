module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY28 : integerGapOK AZY ((54303 / 125000 : ℚ),(2172121 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY28 : shiftedColumnBracketOK C Vc V AY QY MY ((54303 / 125000 : ℚ),(2172121 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
