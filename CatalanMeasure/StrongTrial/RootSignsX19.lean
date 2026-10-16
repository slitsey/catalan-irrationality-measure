module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignX152 : (rootX152).signCheck AZX=true := by
  decide +kernel
theorem rootSignX153 : (rootX153).signCheck AZX=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
