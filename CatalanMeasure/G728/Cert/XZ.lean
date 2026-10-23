module
public import CatalanMeasure.G728.Cert.XTab
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.G728.Data
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem D_X_Z : D_X.Z = rowZ Pc Vc := by decide +kernel
theorem hZ_X : ∀ x : ℝ, -4 * finUR Pc x - finPR Vc x = ptZ D_X.Z 0 x := by
  intro x
  rw [D_X_Z]
  exact rowZ_spec Pc Vc x
end CatalanMeasure.G728
