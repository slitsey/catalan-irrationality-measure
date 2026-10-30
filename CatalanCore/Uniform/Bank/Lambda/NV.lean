import CatalanCore.Uniform.Bank.Lambda.Geom
import CatalanCore.Uniform.Frame.NVAdapter
set_option Elab.async false



namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

theorem FL_nv0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : FL.selectionDepth Fr 2 ≤ depth) : HasNV0 (FL.family Fr depth) FL.scale :=
  FL.hasNV0 Fr 2 depth (by norm_num) hd hw
    (fun i => by simp [FL, altGeom, single, commonB])
    (fun i => by simp [FL, altGeom, single, rowB])
    (fun i => by simp [FL, altGeom, single, colB]) hdepth

end CatalanCore.Uniform.Bank.Lambda
