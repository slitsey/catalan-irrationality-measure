module
public import CatalanMeasure.StrongTrial.RootData
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert Polynomial Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem rootSignY24 : (rootY24).signCheck AZY=true := by
  decide +kernel
theorem rootSignY25 : (rootY25).signCheck AZY=true := by
  decide +kernel
theorem rootSignY26 : (rootY26).signCheck AZY=true := by
  decide +kernel
theorem rootSignY27 : (rootY27).signCheck AZY=true := by
  decide +kernel
theorem rootSignY28 : (rootY28).signCheck AZY=true := by
  decide +kernel
theorem rootSignY29 : (rootY29).signCheck AZY=true := by
  decide +kernel
theorem rootSignY30 : (rootY30).signCheck AZY=true := by
  decide +kernel
theorem rootSignY31 : (rootY31).signCheck AZY=true := by
  decide +kernel
end CatalanMeasure.StrongTrial
