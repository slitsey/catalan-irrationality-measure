module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY68 : integerGapOK AZY ((1997093 / 2000000 : ℚ),(9985467 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY68 : shiftedColumnBracketOK C Vc V AY QY MY ((1997093 / 2000000 : ℚ),(9985467 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
