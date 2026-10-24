module
public import CatalanArchive.CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY0 : (rootY0).signCheck AZY=true := by
  exact coarseEndpointPilotY
theorem rootSignY1 : (rootY1).signCheck AZY=true := by
  decide +kernel
theorem rootSignY2 : (rootY2).signCheck AZY=true := by
  decide +kernel
theorem rootSignY3 : (rootY3).signCheck AZY=true := by
  decide +kernel
theorem rootSignY4 : (rootY4).signCheck AZY=true := by
  decide +kernel
theorem rootSignY5 : (rootY5).signCheck AZY=true := by
  decide +kernel
theorem rootSignY6 : (rootY6).signCheck AZY=true := by
  decide +kernel
theorem rootSignY7 : (rootY7).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
