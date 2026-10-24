module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY8 : integerGapOK AZY ((182639 / 2500000 : ℚ),(187 / 2000 : ℚ),false)=true :=by decide +kernel
theorem bracketY8 : shiftedColumnBracketOK C Vc V AY QY MY ((182639 / 2500000 : ℚ),(187 / 2000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
