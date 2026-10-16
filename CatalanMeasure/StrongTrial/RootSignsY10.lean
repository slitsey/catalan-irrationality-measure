module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY80 : (rootY80).signCheck AZY=true := by
  decide +kernel
theorem rootSignY81 : (rootY81).signCheck AZY=true := by
  decide +kernel
theorem rootSignY82 : (rootY82).signCheck AZY=true := by
  decide +kernel
theorem rootSignY83 : (rootY83).signCheck AZY=true := by
  decide +kernel
theorem rootSignY84 : (rootY84).signCheck AZY=true := by
  decide +kernel
theorem rootSignY85 : (rootY85).signCheck AZY=true := by
  decide +kernel
theorem rootSignY86 : (rootY86).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
