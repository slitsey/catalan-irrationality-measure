module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY55 : integerGapOK AZY ((4235409 / 5000000 : ℚ),(423541 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY55 : shiftedColumnBracketOK C Vc V AY QY MY ((4235409 / 5000000 : ℚ),(423541 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
