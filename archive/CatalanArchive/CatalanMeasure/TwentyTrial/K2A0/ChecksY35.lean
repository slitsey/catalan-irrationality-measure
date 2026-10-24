module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY35 : integerGapOK AZY ((2647139 / 5000000 : ℚ),(5294281 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY35 : shiftedColumnBracketOK C Vc V AY QY MY ((2647139 / 5000000 : ℚ),(5294281 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
