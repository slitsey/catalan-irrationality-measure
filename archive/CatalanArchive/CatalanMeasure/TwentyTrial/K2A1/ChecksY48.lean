module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY48 : integerGapOK AZY ((3 / 4 : ℚ),(3793909 / 5000000 : ℚ),false)=true :=by decide +kernel
theorem bracketY48 : shiftedColumnBracketOK C Vc V AY QY MY ((3 / 4 : ℚ),(3793909 / 5000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
