module

public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.YTab
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.ZChain
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.GenD.D58.Cert.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem D_Y_Z : D_Y.toD.Z = colZ Vc := by
  rw [PolyDataS.toD_Z, colZ, uSum_Vc]
  exact shl_eq_of_zsc _ _ 2 (by decide +kernel)
theorem hZ_Y : ∀ x : ℝ, 2 * finUR Vc x = ptZ D_Y.toD.Z 0 x := by
  intro x
  rw [D_Y_Z]
  exact colZ_spec Vc x
end CatalanMeasure.GenD.D58.Cert
