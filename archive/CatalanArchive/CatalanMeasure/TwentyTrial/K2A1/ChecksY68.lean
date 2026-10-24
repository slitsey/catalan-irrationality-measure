module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY68 : integerGapOK AZY ((2380329 / 2500000 : ℚ),(969 / 1000 : ℚ),false)=true :=by decide +kernel
theorem bracketY68 : shiftedColumnBracketOK C Vc V AY QY MY ((2380329 / 2500000 : ℚ),(969 / 1000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A1
