module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignX8 : (rootX8).signCheck AZX=true := by
  decide +kernel
theorem rootSignX9 : (rootX9).signCheck AZX=true := by
  decide +kernel
theorem rootSignX10 : (rootX10).signCheck AZX=true := by
  decide +kernel
theorem rootSignX11 : (rootX11).signCheck AZX=true := by
  decide +kernel
theorem rootSignX12 : (rootX12).signCheck AZX=true := by
  decide +kernel
theorem rootSignX13 : (rootX13).signCheck AZX=true := by
  decide +kernel
theorem rootSignX14 : (rootX14).signCheck AZX=true := by
  decide +kernel
theorem rootSignX15 : (rootX15).signCheck AZX=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
