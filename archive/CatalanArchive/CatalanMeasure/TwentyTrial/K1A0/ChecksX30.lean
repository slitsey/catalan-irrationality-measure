module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX30 : integerGapOK AZX ((313 / 2000 : ℚ),(420071 / 2500000 : ℚ),false)=true :=by decide +kernel
theorem bracketX30 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((313 / 2000 : ℚ),(420071 / 2500000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A0
