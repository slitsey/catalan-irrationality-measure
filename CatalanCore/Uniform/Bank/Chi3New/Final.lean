import CatalanCore.Uniform.Bank.Chi3New.Decay
import CatalanCore.Uniform.Bank.Chi3New.Content
import CatalanCore.Uniform.Bank.Chi3New.Reindex4
import CatalanCore.Uniform.Content.Bridge.Hybrid
import CatalanFrames.P6.Const
import CatalanCore.Measure.Scaling
set_option Elab.async false

/-! The irrationality measure of `L(2, χ₋₃)` from the chi3 block family (lane B, B3f).

Content (B3c, `Λ = 4744590251372789/1155228423148800`, scales `≡ 0 mod 4`) + window decay (B3b
tables, `D = Dt`, `c = ccert`) + `HasNV0` of the block family give
`μ(p6Frame.const) ≤ ccert / (Dt - Λ) < 13.9889`, and the affine transfer `L(2,χ₋₃) = 4 · p6Frame.const`
gives the same exponent for `L(2, χ₋₃)`. -/

namespace CatalanCore.Uniform.Bank.Chi3New
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.P6
  CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Chi3Content

theorem Dchi_Dt : Dchi.Dt = 4643511791526209475773 / 1000000000000000000000 := by decide +kernel
theorem Dchi_ccert : Dchi.ccert = 37521870783566737 / 5000000000000000 := by decide +kernel

theorem G12_common_mass : G12.common.mass = 1 := by
  simp [G12, altGeom, single_mass, commonB, PeriodicBlock.mass]

/-- A selection depth that works for the chi3 geometry (period `L = 2`). -/
noncomputable def depth0 : ℕ := G12.selectionDepth p6Frame 2

theorem p6_w_ne (i : Fin p6Frame.d) : p6Frame.w i ≠ 0 := by
  rcases i with ⟨k, hk⟩
  have hk3 : k < 3 := hk
  interval_cases k
  · exact (by decide : (1 : ℤ) ≠ 0)
  · exact (by decide : (2 : ℤ) ≠ 0)
  · exact (by decide : (-3 : ℤ) ≠ 0)

theorem chi3_nv0 : HasNV0 (G12.family p6Frame depth0) G12.scale :=
  G12.hasNV0 p6Frame 2 depth0 (by norm_num) (by show 1 ≤ 3; norm_num) p6_w_ne
    (fun i => by simp [G12, altGeom, single, commonB])
    (fun i => by simp [G12, altGeom, single, rowB])
    (fun i => by simp [G12, altGeom, single, colB]) le_rfl

end CatalanCore.Uniform.Bank.Chi3New
