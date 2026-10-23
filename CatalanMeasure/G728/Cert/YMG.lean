module
public import CatalanMeasure.G728.CellW
public import CatalanMeasure.G728.MGNDefsY
public import CatalanMeasure.G728.MGNChunkY0
public import CatalanMeasure.G728.MGNChunkY1
public import CatalanMeasure.G728.MGNChunkY2
public import CatalanMeasure.G728.MGNChunkY3
public import CatalanMeasure.G728.Cert.YTab
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem tNY_end : tfoldN ((((((((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) tNY19 = tNY19 := by decide +kernel
theorem tfoldN_Bsp_Y : tfoldN Bsp_Y (([2], [0, 1]), []) = tNY19 :=
  tfoldN_chain (Bsp_Y) 30 tNY_c0 (tfoldN_chain ((Bsp_Y).drop 30) 30 tNY_c1 (tfoldN_chain (((Bsp_Y).drop 30).drop 30) 30 tNY_c2 (tfoldN_chain ((((Bsp_Y).drop 30).drop 30).drop 30) 30 tNY_c3 (tfoldN_chain (((((Bsp_Y).drop 30).drop 30).drop 30).drop 30) 30 tNY_c4 (tfoldN_chain ((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c5 (tfoldN_chain (((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c6 (tfoldN_chain ((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c7 (tfoldN_chain (((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c8 (tfoldN_chain ((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c9 (tfoldN_chain (((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c10 (tfoldN_chain ((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c11 (tfoldN_chain (((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c12 (tfoldN_chain ((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c13 (tfoldN_chain (((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c14 (tfoldN_chain ((((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c15 (tfoldN_chain (((((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c16 (tfoldN_chain ((((((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c17 (tfoldN_chain (((((((((((((((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30) 30 tNY_c18 (tNY_end)))))))))))))))))))
theorem tcomb_Y : tcomb Bs_Y = zsc (2 ^ Np_Y) (wlist 70 D_Y.Z) :=
  tcomb_of_N _ Bsp_Y _ (2 ^ 139) _ (by decide +kernel) tfoldN_Bsp_Y
    (by rw [shl_two_eq_mapIdx, PolyData.Z, shl_eq_mapIdx]; decide +kernel)
theorem hMGL_Y : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D_Y.Z (5 + 65) y| ≤ (MGL_Y : ℝ) :=
  poly_sup_of D_Y.Z (5 + 65) Bs_Y MGL_Y Np_Y tcomb_Y (by decide +kernel)
end CatalanMeasure.G728
