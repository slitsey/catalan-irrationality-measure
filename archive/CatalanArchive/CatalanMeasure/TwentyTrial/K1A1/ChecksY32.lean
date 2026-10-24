module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY32 : integerGapOK AZY ((6736839 / 10000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY32 : shiftedColumnBracketOK C Vc V AY QY MY ((6736839 / 10000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
