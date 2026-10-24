module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY17 : integerGapOK AZY ((453711 / 2500000 : ℚ),(907423 / 5000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY17 : shiftedColumnBracketOK C Vc V AY QY MY ((453711 / 2500000 : ℚ),(907423 / 5000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
