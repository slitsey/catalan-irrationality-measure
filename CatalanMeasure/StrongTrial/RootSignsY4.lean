module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY32 : (rootY32).signCheck AZY=true := by
  decide +kernel
theorem rootSignY33 : (rootY33).signCheck AZY=true := by
  decide +kernel
theorem rootSignY34 : (rootY34).signCheck AZY=true := by
  decide +kernel
theorem rootSignY35 : (rootY35).signCheck AZY=true := by
  decide +kernel
theorem rootSignY36 : (rootY36).signCheck AZY=true := by
  decide +kernel
theorem rootSignY37 : (rootY37).signCheck AZY=true := by
  decide +kernel
theorem rootSignY38 : (rootY38).signCheck AZY=true := by
  decide +kernel
theorem rootSignY39 : (rootY39).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
