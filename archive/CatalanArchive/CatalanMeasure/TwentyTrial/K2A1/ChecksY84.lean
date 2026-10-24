module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY84 : integerGapOK AZY ((9980549 / 10000000 : ℚ),(49951 / 50000 : ℚ),false)=true :=by decide +kernel
theorem bracketY84 : shiftedColumnBracketOK C Vc V AY QY MY ((9980549 / 10000000 : ℚ),(49951 / 50000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
