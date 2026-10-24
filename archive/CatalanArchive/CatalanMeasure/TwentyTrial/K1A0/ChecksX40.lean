module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX40 : integerGapOK AZX ((695357 / 2000000 : ℚ),(869197 / 2500000 : ℚ),true)=true :=by decide +kernel
theorem bracketX40 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((695357 / 2000000 : ℚ),(869197 / 2500000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
