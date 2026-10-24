module
public import CatalanArchive.CatalanMeasure.TwentyTrial.K1A1.Data
@[expose] public section
namespace CatalanMeasure.TwentyTrial.K1A1
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem gapX61 : integerGapOK AZX ((5155621 / 10000000 : ℚ),(5155623 / 10000000 : ℚ),true)=true :=by decide +kernel
theorem bracketX61 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((5155621 / 10000000 : ℚ),(5155623 / 10000000 : ℚ),true)=true :=by decide +kernel
end CatalanMeasure.TwentyTrial.K1A1
