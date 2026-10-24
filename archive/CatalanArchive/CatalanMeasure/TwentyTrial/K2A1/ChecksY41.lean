module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY41 : integerGapOK AZY ((3230371 / 5000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
theorem bracketY41 : shiftedColumnBracketOK C Vc V AY QY MY ((3230371 / 5000000 : ℚ),(86 / 125 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
