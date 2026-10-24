module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY22 : integerGapOK AZY ((2465989 / 5000000 : ℚ),(246599 / 500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY22 : shiftedColumnBracketOK C Vc V AY QY MY ((2465989 / 5000000 : ℚ),(246599 / 500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
