module

public import CatalanMeasure.GenD.D58.Cert.RTab
public import CatalanMeasure.GenD.D58.Cert.ZChain
public import CatalanMeasure.G728.PolyZ
public import CatalanMeasure.GenD.D58.Cert.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem D_R_Z : D_R.toD.Z = resZ Pc := by
  rw [PolyDataS.toD_Z, resZ, uSum_Pc]
  exact shl_eq_of_zsc _ _ (-2) (by decide +kernel)
theorem hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x := by
  intro x
  rw [D_R_Z]
  exact resZ_spec Pc x
end CatalanMeasure.GenD.D58.Cert
