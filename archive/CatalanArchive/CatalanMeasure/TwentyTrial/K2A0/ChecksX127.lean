module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K2A0.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K2A0
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX127 : integerGapOK AZX ((1687 / 2000 : ℚ),(8549919 / 10000000 : ℚ),false)=true :=by decide +kernel
theorem bracketX127 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((1687 / 2000 : ℚ),(8549919 / 10000000 : ℚ),false)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K2A0
