module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY16 : (rootY16).signCheck AZY=true := by
  decide +kernel
theorem rootSignY17 : (rootY17).signCheck AZY=true := by
  decide +kernel
theorem rootSignY18 : (rootY18).signCheck AZY=true := by
  decide +kernel
theorem rootSignY19 : (rootY19).signCheck AZY=true := by
  decide +kernel
theorem rootSignY20 : (rootY20).signCheck AZY=true := by
  decide +kernel
theorem rootSignY21 : (rootY21).signCheck AZY=true := by
  decide +kernel
theorem rootSignY22 : (rootY22).signCheck AZY=true := by
  decide +kernel
theorem rootSignY23 : (rootY23).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
