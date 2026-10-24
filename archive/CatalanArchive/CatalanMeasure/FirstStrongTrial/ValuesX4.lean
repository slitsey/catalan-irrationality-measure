module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem bracketX_49 : shiftedRowBracketOK R Pc Vc P V AX QX MX ((78043533 / 100000000 : ℚ),(4877721 / 6250000 : ℚ),true)=true := by decide +kernel
end CatalanMeasure.FirstStrongTrial
