import CatalanCore.Uniform.Bank.Halves.Geom
import CatalanCore.Uniform.Frame.NVAdapter
set_option Elab.async false

/-! Nonvanishing of the halves block family (lane B, B5): `HasNV0` from the generic selector, for
every frame with nonzero weights, at the selection depth for period `L = 2`. -/

namespace CatalanCore.Uniform.Bank.Halves
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

theorem FH_nv0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : FH.selectionDepth Fr 2 ≤ depth) : HasNV0 (FH.family Fr depth) FH.scale :=
  FH.hasNV0 Fr 2 depth (by norm_num) hd hw
    (fun i => by simp [FH, altGeom, single, commonB])
    (fun i => by simp [FH, altGeom, single, rowB])
    (fun i => by simp [FH, altGeom, single, colB]) hdepth

end CatalanCore.Uniform.Bank.Halves
