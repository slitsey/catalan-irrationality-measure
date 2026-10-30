import CatalanCore.Uniform.Bank.Chi3Rank.RankSum
import CatalanCore.Uniform.Bank.Chi3New.Final
set_option Elab.async false

/-! # The irrationality measure of `L(2, χ₋₃)` with the rank layer (lane H, H16)

B3f's `Chi3New.chi3_measureLB` with the content `Λ' = Λ - 3/320 = 4733759984905769/1155228423148800`
(`Dnew2`, i.e. tropical + M3D + rank layer, at scales `r ≡ 0 mod 4`):
`μ(L(2, χ₋₃)) ≤ ccert / (Dt - Λ') < 13.7486`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanFrames.P6
  CatalanFrames.P6Hybrid CatalanCore.Uniform.Bank.Chi3Content CatalanCore.Uniform.Bank.Chi3New
  CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.Cert

/-- **Scaled content of the chi3 block family at scales `≡ 0 mod 4`, with the rank layer.** -/
theorem hasScaledContent_chi3_rank (depth : ℕ) :
    HasScaledContent ((G12.family p6Frame depth).restrictAdm (fun i => i.1 % 4 = 0)) G12.scale
      (LamRank : ℝ) := by
  refine ⟨fun i => Dnew2 i.1 (G12.geometry i.1).k, fun i => Dnew2_pos _ _, ?_, ?_⟩
  · intro i hi p q hq
    have hr2 : i.1 % 2 = 0 := by have := hi.2; omega
    obtain ⟨s, hQ⟩ := G12_poly_eq p6Frame hr2 i.2
    have hQ' : (G12.family p6Frame depth).Q i = commonMinorPoly p6Frame i.1 (G12.geometry i.1).k s :=
      hQ
    exact Content.Member.int_clear' ((G12.family p6Frame depth).Q i) i.2.card
      (NodeFamily.polynomial_degree p6Frame G12.geometry i) (Dnew2 i.1 (G12.geometry i.1).k)
      (fun j => by rw [hQ']; exact Dnew2_integral i.1 _ s j) p q hq
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (log_content_rank ε hε)
    refine ⟨N, fun i hi hR => ?_⟩
    have hk := G12_k hi.2
    have h4 := hi.2
    exact hN i.1 hR _ ⟨G12_adm h4, by omega⟩

/-- **Measure of the block family with the rank layer.** -/
theorem chi3_measureLB_rank :
    (G12.family p6Frame depth0).MeasureLB
      ((1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
        (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - (LamRank : ℝ))) := by
  have hmass : (G12.common.mass : ℝ) = 1 := by rw [G12_common_mass]; norm_num
  have hS := hasScaledContent_chi3_rank depth0
  have hD0 := chi3_decay depth0
  rw [Dchi_Dt, Dchi_ccert] at hD0
  have hD : HasScaledDecay ((G12.family p6Frame depth0).restrictAdm (fun i => i.1 % 4 = 0))
      G12.scale (4643511791526209475773 / 1000000000000000000000 : ℚ)
      (37521870783566737 / 5000000000000000 : ℚ) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD0 ε hε
    exact ⟨R0, fun n hn => h n hn.1⟩
  have hη : (LamRank : ℝ) < ((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) := by
    unfold LamRank; push_cast; norm_num
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

theorem chi3_X_le_rank : (1 : ℝ) * ((37521870783566737 / 5000000000000000 : ℚ) : ℝ) /
    (((4643511791526209475773 / 1000000000000000000000 : ℚ) : ℝ) - (LamRank : ℝ)) ≤
      ((137486 / 10000 : ℚ) : ℝ) := by
  have hL : (LamRank : ℝ) = 4733759984905769 / 1155228423148800 := by
    unfold LamRank; push_cast; norm_num
  rw [hL]
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- **`μ(L(2, χ₋₃)) ≤ 13.7486`** (certified exponent `ccert / (Dt - Λ') = 13.74858862…`). -/
theorem chi3_measure_L2_rank : Measure.MeasureLBAt chi3L2 ((137486 / 10000 : ℚ) : ℝ) := by
  have h0 := (Measure.MeasureLB_iff _ _).mp chi3_measureLB_rank
  have h' : Measure.MeasureLBAt p6Frame.const ((137486 / 10000 : ℚ) : ℝ) :=
    Measure.MeasureLBAt.mono chi3_X_le_rank h0
  have he : chi3L2 = ((4 : ℚ) : ℝ) * p6Frame.const + ((0 : ℚ) : ℝ) := by
    rw [p6Frame_const]; push_cast; ring
  rw [he]
  exact h'.affine (by norm_num) 4 0 (by norm_num)

end CatalanCore.Uniform.Bank.Chi3Rank
