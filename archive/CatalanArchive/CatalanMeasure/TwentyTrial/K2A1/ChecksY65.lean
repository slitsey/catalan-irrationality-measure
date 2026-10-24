module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY65 : integerGapOK AZY ((9325477 / 10000000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY65 : shiftedColumnBracketOK C Vc V AY QY MY ((9325477 / 10000000 : ℚ),(469 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
