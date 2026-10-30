module

public import CatalanCore.Uniform.Bank.Fifths.Geom
public import CatalanCore.Uniform.Frame.NVAdapter

@[expose] public section
set_option Elab.async false

/-! Nonvanishing of the fifths block family (lane B, B5): `HasNV0` from the generic selector, for
every frame with nonzero weights, at the selection depth for period `L = 2`. -/

namespace CatalanCore.Uniform.Bank.Fifths
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

theorem F5_nv0 (Fr : Frame) (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) (depth : ℕ)
    (hdepth : F5.selectionDepth Fr 2 ≤ depth) : HasNV0 (F5.family Fr depth) F5.scale :=
  F5.hasNV0 Fr 2 depth (by norm_num) hd hw
    (fun i => by simp [F5, altGeom, single, commonB])
    (fun i => by simp [F5, altGeom, single, rowB])
    (fun i => by simp [F5, altGeom, single, colB]) hdepth

end CatalanCore.Uniform.Bank.Fifths
