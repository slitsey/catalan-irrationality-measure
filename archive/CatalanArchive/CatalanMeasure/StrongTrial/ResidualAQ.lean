module
public import CatalanArchive.CatalanMeasure.StrongTrial.ResidualData
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidual
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem hAQR : fracSum (markedResidualFracs Pc P)=(AR,QR) := by decide +kernel
end CatalanMeasure.StrongTrial
