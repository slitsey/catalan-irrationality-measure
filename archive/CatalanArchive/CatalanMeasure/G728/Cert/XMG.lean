module
public import CatalanMeasure.G728.CellW
public import CatalanArchive.CatalanMeasure.G728.MGNDefsX
public import CatalanArchive.CatalanMeasure.G728.MGNChunkX0
public import CatalanArchive.CatalanMeasure.G728.MGNChunkX1
public import CatalanArchive.CatalanMeasure.G728.MGNChunkX2
public import CatalanArchive.CatalanMeasure.G728.MGNChunkX3
public import CatalanArchive.CatalanMeasure.G728.Cert.XTab
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem tNX_end : tfoldN ((((((((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) tNX19 = tNX19 := by decide +kernel
theorem tfoldN_Bsp_X : tfoldN Bsp_X (([2], [0, 1]), []) = tNX19 :=
  tfoldN_chain (Bsp_X) 30 tNX_c0 (tfoldN_chain ((Bsp_X).drop 30) 30 tNX_c1 (tfoldN_chain (((Bsp_X).drop 30).drop 30) 30 tNX_c2 (tfoldN_chain ((((Bsp_X).drop 30).drop 30).drop 30) 30 tNX_c3 (tfoldN_chain (((((Bsp_X).drop 30).drop 30).drop 30).drop 30) 30 tNX_c4 (tfoldN_chain ((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c5 (tfoldN_chain (((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c6 (tfoldN_chain ((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c7 (tfoldN_chain (((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c8 (tfoldN_chain ((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c9 (tfoldN_chain (((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c10 (tfoldN_chain ((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c11 (tfoldN_chain (((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c12 (tfoldN_chain ((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c13 (tfoldN_chain (((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c14 (tfoldN_chain ((((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c15 (tfoldN_chain (((((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c16 (tfoldN_chain ((((((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c17 (tfoldN_chain (((((((((((((((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNX_c18 (tNX_end)))))))))))))))))))
theorem tcomb_X : tcomb Bs_X = zsc (2 ^ Np_X) (wlist 70 D_X.Z) :=
  tcomb_of_N _ Bsp_X _ 1 _ (by simp [zsc, Bsp_X]) tfoldN_Bsp_X
    (by rw [shl_two_eq_mapIdx, PolyData.Z, shl_eq_mapIdx]; decide +kernel)
theorem hMGL_X : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D_X.Z (5 + 65) y| ≤ (MGL_X : ℝ) :=
  poly_sup_of D_X.Z (5 + 65) Bs_X MGL_X Np_X tcomb_X (by decide +kernel)
end CatalanMeasure.G728
