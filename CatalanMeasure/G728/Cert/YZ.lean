module
public import CatalanMeasure.G728.Cert.YTab
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.G728.Data
@[expose] public section
namespace CatalanMeasure.G728
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem D_Y_Z : D_Y.Z = colZ Vc := by decide +kernel
theorem hZ_Y : ∀ x : ℝ, 2 * finUR Vc x = ptZ D_Y.Z 0 x := by
  intro x
  rw [D_Y_Z]
  exact colZ_spec Vc x
end CatalanMeasure.G728
