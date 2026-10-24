module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY1 : integerGapOK AZY ((282061 / 10000000 : ℚ),(282063 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY1 : shiftedColumnBracketOK C Vc V AY QY MY ((282061 / 10000000 : ℚ),(282063 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
