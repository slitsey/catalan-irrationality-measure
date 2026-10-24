module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX63 : integerGapOK AZX ((719 / 1000 : ℚ),(7292917 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX63 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((719 / 1000 : ℚ),(7292917 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
