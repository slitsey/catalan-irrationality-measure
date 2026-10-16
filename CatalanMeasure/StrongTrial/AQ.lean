module
public import CatalanMeasure.StrongTrial.FieldsData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem hAQX : fracSum (shiftedRowFracs R Pc Vc P V) = (AX,QX) := by decide +kernel
theorem hAQY : fracSum (shiftedColumnFracs C Vc V) = (AY,QY) := by decide +kernel
end CatalanMeasure.StrongTrial
