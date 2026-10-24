module

public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.XTab
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.ZChain
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.GenD.D58.Cert.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem D_X_Z : D_X.toD.Z = rowZ Pc Vc := by
  rw [PolyDataS.toD_Z, show D_X.lam = 1 from rfl, shl_eq_mapIdx, rowZ, uSum_Pc, shl_two_eq_mapIdx]; decide +kernel
theorem hZ_X : ∀ x : ℝ, -4 * finUR Pc x - finPR Vc x = ptZ D_X.toD.Z 0 x := by
  intro x
  rw [D_X_Z]
  exact rowZ_spec Pc Vc x
end CatalanMeasure.GenD.D58.Cert
