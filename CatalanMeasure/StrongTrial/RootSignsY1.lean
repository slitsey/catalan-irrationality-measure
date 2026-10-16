module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY8 : (rootY8).signCheck AZY=true := by
  decide +kernel
theorem rootSignY9 : (rootY9).signCheck AZY=true := by
  decide +kernel
theorem rootSignY10 : (rootY10).signCheck AZY=true := by
  decide +kernel
theorem rootSignY11 : (rootY11).signCheck AZY=true := by
  decide +kernel
theorem rootSignY12 : (rootY12).signCheck AZY=true := by
  decide +kernel
theorem rootSignY13 : (rootY13).signCheck AZY=true := by
  decide +kernel
theorem rootSignY14 : (rootY14).signCheck AZY=true := by
  decide +kernel
theorem rootSignY15 : (rootY15).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
