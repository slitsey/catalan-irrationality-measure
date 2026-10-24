module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY64 : integerGapOK AZY ((9961 / 10000 : ℚ),(1245673 / 1250000 : ℚ),false)=true :=by decide +kernel
theorem bracketY64 : shiftedColumnBracketOK C Vc V AY QY MY ((9961 / 10000 : ℚ),(1245673 / 1250000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
