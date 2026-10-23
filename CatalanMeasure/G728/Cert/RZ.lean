module
public import CatalanMeasure.G728.Cert.RTab
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.G728.Data
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem D_R_Z : D_R.Z = resZ Pc := by decide +kernel
theorem hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.Z 0 x := by
  intro x
  rw [D_R_Z]
  exact resZ_spec Pc x
end CatalanMeasure.G728
