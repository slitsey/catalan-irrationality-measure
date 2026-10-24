module
public import CatalanArchive.CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY40 : (rootY40).signCheck AZY=true := by
  decide +kernel
theorem rootSignY41 : (rootY41).signCheck AZY=true := by
  decide +kernel
theorem rootSignY42 : (rootY42).signCheck AZY=true := by
  decide +kernel
theorem rootSignY43 : (rootY43).signCheck AZY=true := by
  decide +kernel
theorem rootSignY44 : (rootY44).signCheck AZY=true := by
  decide +kernel
theorem rootSignY45 : (rootY45).signCheck AZY=true := by
  decide +kernel
theorem rootSignY46 : (rootY46).signCheck AZY=true := by
  decide +kernel
theorem rootSignY47 : (rootY47).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
