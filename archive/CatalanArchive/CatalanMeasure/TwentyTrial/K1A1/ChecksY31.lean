module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY31 : integerGapOK AZY ((6736837 / 10000000 : ℚ),(6736839 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY31 : shiftedColumnBracketOK C Vc V AY QY MY ((6736837 / 10000000 : ℚ),(6736839 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
