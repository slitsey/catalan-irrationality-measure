module

public import CatalanCore.Uniform.Bank.Sevenths.Geom
public import CatalanCore.Uniform.Frame.NVAdapter

@[expose] public section
set_option Elab.async false

/-! Nonvanishing of the sevenths block family (lane B, B5): `HasNV0` from the generic selector, for
every frame with nonzero weights, at the selection depth for period `L = 2`. -/

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

theorem F7_nv0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F7.selectionDepth Fr 2 ≤ depth) : HasNV0 (F7.family Fr depth) F7.scale :=
  F7.hasNV0 Fr 2 depth (by norm_num) hd hw
    (fun i => by simp [F7, altGeom, single, commonB])
    (fun i => by simp [F7, altGeom, single, rowB])
    (fun i => by simp [F7, altGeom, single, colB]) hdepth

end CatalanCore.Uniform.Bank.Sevenths
