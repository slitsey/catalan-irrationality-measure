module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY40 : integerGapOK AZY ((8132209 / 10000000 : ℚ),(2033053 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY40 : shiftedColumnBracketOK C Vc V AY QY MY ((8132209 / 10000000 : ℚ),(2033053 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
