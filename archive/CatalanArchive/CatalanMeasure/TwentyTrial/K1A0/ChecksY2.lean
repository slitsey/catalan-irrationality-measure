module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY2 : integerGapOK AZY ((282063 / 10000000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
theorem bracketY2 : shiftedColumnBracketOK C Vc V AY QY MY ((282063 / 10000000 : ℚ),(31 / 500 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
