module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY11 : integerGapOK AZY ((110799 / 1250000 : ℚ),(443197 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY11 : shiftedColumnBracketOK C Vc V AY QY MY ((110799 / 1250000 : ℚ),(443197 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
