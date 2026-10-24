module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY42 : integerGapOK AZY ((86 / 125 : ℚ),(6920069 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY42 : shiftedColumnBracketOK C Vc V AY QY MY ((86 / 125 : ℚ),(6920069 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
