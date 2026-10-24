module
public import CatalanMeasure.G728.CellW
public import CatalanArchive.CatalanMeasure.G728.MGNDefsR
public import CatalanArchive.CatalanMeasure.G728.MGNChunkR0
public import CatalanArchive.CatalanMeasure.G728.MGNChunkR1
public import CatalanArchive.CatalanMeasure.G728.MGNChunkR2
public import CatalanArchive.CatalanMeasure.G728.MGNChunkR3
public import CatalanArchive.CatalanMeasure.G728.Cert.RTab
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem tNR_end : tfoldN ((((((((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) tNR19 = tNR19 := by decide +kernel
theorem tfoldN_Bsp_R : tfoldN Bsp_R (([2], [0, 1]), []) = tNR19 :=
  tfoldN_chain (Bsp_R) 30 tNR_c0 (tfoldN_chain ((Bsp_R).drop 30) 30 tNR_c1 (tfoldN_chain (((Bsp_R).drop 30).drop 30) 30 tNR_c2 (tfoldN_chain ((((Bsp_R).drop 30).drop 30).drop 30) 30 tNR_c3 (tfoldN_chain (((((Bsp_R).drop 30).drop 30).drop 30).drop 30) 30 tNR_c4 (tfoldN_chain ((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c5 (tfoldN_chain (((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c6 (tfoldN_chain ((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c7 (tfoldN_chain (((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c8 (tfoldN_chain ((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c9 (tfoldN_chain (((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c10 (tfoldN_chain ((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c11 (tfoldN_chain (((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c12 (tfoldN_chain ((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c13 (tfoldN_chain (((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c14 (tfoldN_chain ((((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c15 (tfoldN_chain (((((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c16 (tfoldN_chain ((((((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c17 (tfoldN_chain (((((((((((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNR_c18 (tNR_end)))))))))))))))))))
theorem tcomb_R : tcomb Bs_R = zsc (2 ^ Np_R) (wlist 70 D_R.Z) :=
  tcomb_of_N _ Bsp_R _ (2 ^ 138) _ (by decide +kernel) tfoldN_Bsp_R
    (by rw [shl_two_eq_mapIdx, PolyData.Z, shl_eq_mapIdx]; decide +kernel)
theorem hMGL_R : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D_R.Z (5 + 65) y| ≤ (MGL_R : ℝ) :=
  poly_sup_of D_R.Z (5 + 65) Bs_R MGL_R Np_R tcomb_R (by decide +kernel)
end CatalanMeasure.G728
