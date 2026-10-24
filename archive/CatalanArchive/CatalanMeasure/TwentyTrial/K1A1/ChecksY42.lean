module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY42 : integerGapOK AZY ((1687 / 2000 : ℚ),(8567067 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY42 : shiftedColumnBracketOK C Vc V AY QY MY ((1687 / 2000 : ℚ),(8567067 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
