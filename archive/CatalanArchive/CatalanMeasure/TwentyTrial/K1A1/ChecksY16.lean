module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY16 : integerGapOK AZY ((720701 / 2000000 : ℚ),(3603507 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY16 : shiftedColumnBracketOK C Vc V AY QY MY ((720701 / 2000000 : ℚ),(3603507 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
