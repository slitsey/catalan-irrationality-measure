module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapY55 : integerGapOK AZY ((4828021 / 5000000 : ℚ),(2414011 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketY55 : shiftedColumnBracketOK C Vc V AY QY MY ((4828021 / 5000000 : ℚ),(2414011 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
