module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY31 : integerGapOK AZY ((6693821 / 10000000 : ℚ),(6693823 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY31 : shiftedColumnBracketOK C Vc V AY QY MY ((6693821 / 10000000 : ℚ),(6693823 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
