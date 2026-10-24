module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY4 : integerGapOK AZY ((77833 / 2000000 : ℚ),(24323 / 625000 : ℚ),true)=true :=by decide +kernel
theorem bracketY4 : shiftedColumnBracketOK C Vc V AY QY MY ((77833 / 2000000 : ℚ),(24323 / 625000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
