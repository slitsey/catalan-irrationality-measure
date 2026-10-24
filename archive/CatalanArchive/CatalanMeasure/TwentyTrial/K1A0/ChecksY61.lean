module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY61 : integerGapOK AZY ((4948973 / 5000000 : ℚ),(9897949 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketY61 : shiftedColumnBracketOK C Vc V AY QY MY ((4948973 / 5000000 : ℚ),(9897949 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
