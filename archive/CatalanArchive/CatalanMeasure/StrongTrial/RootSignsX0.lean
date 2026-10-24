module
public import CatalanArchive.CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignX0 : (rootX0).signCheck AZX=true := by
  decide +kernel
theorem rootSignX1 : (rootX1).signCheck AZX=true := by
  decide +kernel
theorem rootSignX2 : (rootX2).signCheck AZX=true := by
  decide +kernel
theorem rootSignX3 : (rootX3).signCheck AZX=true := by
  decide +kernel
theorem rootSignX4 : (rootX4).signCheck AZX=true := by
  decide +kernel
theorem rootSignX5 : (rootX5).signCheck AZX=true := by
  decide +kernel
theorem rootSignX6 : (rootX6).signCheck AZX=true := by
  decide +kernel
theorem rootSignX7 : (rootX7).signCheck AZX=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
