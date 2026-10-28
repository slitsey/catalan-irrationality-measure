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

/-- **Measure of the block family.** -/
theorem chi3_measureLB :
    (G12.family p6Frame depth0).MeasureLB
      ((1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
        (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - (LamNew : ℝ))) := by
  have hmass : (G12.common.mass : ℝ) = 1 := by rw [G12_common_mass]; norm_num
  have hS := hasScaledContent_chi3 depth0
  have hD0 := chi3_decay depth0
  rw [Dchi_Dt, Dchi_ccert] at hD0
  have hD : HasScaledDecay ((G12.family p6Frame depth0).restrictAdm (fun i => i.1 % 4 = 0))
      G12.scale (4643511791526209475773 / 1000000000000000000000 : ℚ)
      (37521870783566737 / 5000000000000000 : ℚ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD0 ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hη : (LamNew : ℝ) < ((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) := by
    unfold LamNew; push_cast; norm_num
  have hc : (0 : ℝ) < ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) := by norm_num
  have key := measure_of_family_nv0_four
    ((G12.family p6Frame depth0).restrictAdm (fun i => i.1 % 4 = 0)) G12.scale
    (γ := 1) (K := G12.common.n) hS hD hη hc one_pos (Nat.cast_nonneg _)
    (fun n hn => by
      have := G12.degree_bound p6Frame depth0 n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2)
    (by
      obtain ⟨R0, hR⟩ := chi3_nv0
      refine ⟨R0, fun s hs x => ?_⟩
      obtain ⟨n, hn, hsc, hne⟩ := hR (4 * s) (by omega) x
      exact ⟨n, ⟨hn, by have : G12.scale n = n.1 := rfl; omega⟩, hsc, hne⟩)
  exact key

theorem chi3_X_le : (1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
    (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - (LamNew : ℝ)) ≤
      ((139889 / 10000 : ℚ) : ℝ) := by
  have hL : (LamNew : ℝ) = 4744590251372789 / 1155228423148800 := by
    unfold LamNew; push_cast; norm_num
  rw [hL]
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- **`μ(L(2, χ₋₃)) ≤ 13.9889`** (certified exponent `ccert / (Dt - Λ) = 13.98885730…`). -/
theorem chi3_measure_L2 : Measure.MeasureLBAt chi3L2 ((139889 / 10000 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).mp chi3_measureLB
  have h' : Measure.MeasureLBAt p6Frame.const ((139889 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono chi3_X_le h0
  have he : chi3L2 = ((4 : ℚ) : ℝ) * p6Frame.const + ((0 : ℚ) : ℝ) := by
    rw [p6Frame_const]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

end CatalanCore.Uniform.Bank.Chi3New
