module
public import CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY69 : integerGapOK AZY ((969 / 1000 : ℚ),(193929 / 200000 : ℚ),false)=true :=by decide +kernel
theorem bracketY69 : shiftedColumnBracketOK C Vc V AY QY MY ((969 / 1000 : ℚ),(193929 / 200000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
