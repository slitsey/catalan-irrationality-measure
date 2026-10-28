import CatalanCore.Uniform.Bank.Chi3.Decay
import CatalanCore.Uniform.Bank.Chi3New.Energy
import CatalanFrames.P6.Contour
set_option Elab.async false

/-! `HasScaledDecay` of the chi3 block family `G12.family p6Frame depth` (lane B, B3f): the frame
and node hypotheses of `chi3_hasScaledDecay` discharged for `G12 = altGeom (1/2)` and `p6Frame`. -/

namespace CatalanCore.Uniform.Bank.Chi3New
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.P6
  CatalanCore.Uniform.Bank.Chi3 CatalanCore.Uniform.Decay.Cert

theorem Dchi_Inu : Dchi.Inu = 28816875853 / 15625000000 := by decide +kernel
theorem Dchi_eps : Dchi.ε = 1 / 1000 := by decide +kernel
theorem Dchi_dim : Dchi.dim = 3 := by decide +kernel

theorem p6_mu (i : Fin p6Frame.d) :
    (p6Frame.μ i = 1) ∨ (p6Frame.μ i = 1 / 3) ∨ (p6Frame.μ i = 1 / 2) := by
  rcases i with ⟨k, hk⟩
  have hk3 : k < 3 := hk
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem p6_hAR : ∀ i : Fin p6Frame.d, ((⌊p6Frame.xs - p6Frame.μ i⌋ : ℤ) : ℚ) + p6Frame.μ i ≤
    p6Frame.n0off := by
  intro i
  have hx : p6Frame.xs = 3 / 4 := rfl
  have hn : p6Frame.n0off = 1 := rfl
  rw [hx, hn]
  rcases p6_mu i with h | h | h <;> rw [h]
  · have : ⌊(3 / 4 : ℚ) - 1⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    rw [this]; norm_num
  · have : ⌊(3 / 4 : ℚ) - 1 / 3⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
    rw [this]; norm_num
  · have : ⌊(3 / 4 : ℚ) - 1 / 2⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
    rw [this]; norm_num

theorem G12_supp : ∀ r a : ℕ, a ∈ (G12.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (G12.geometry r).C = Finset.range r := altGeom_C _ half_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem G12_blocks_v :
    (∀ i, ((G12.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((G12.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((G12.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [G12, altGeom, single, commonB, rowB, colB]
    try norm_num

/-- **Window decay of the chi3 block family** (`D = Dt`, `c = ccert` of the verified tables). -/
theorem chi3_decay (depth : ℕ) :
    HasScaledDecay (G12.family p6Frame depth) G12.scale (Dchi.Dt : ℝ) (Dchi.ccert : ℝ) := by
  obtain ⟨hc, hr, hq⟩ := G12_blocks_v
  refine chi3_hasScaledDecay G12 p6_contourOK p6_hAR (by norm_num [p6Frame]) G12_rowPieces
    G12_colPieces G12_totalMass.symm (by rw [Dchi_dim]; rfl) ?_ G12_supp (by norm_num) hc hr hq
    (m0 := 1 / 3) (by norm_num) ?_ (e := 1 / 2000) (by norm_num) ?_ depth
  · rw [Dchi_Inu]; exact Inu_le_nodeEnergy
  · intro i
    rcases p6_mu i with h | h | h <;> rw [h] <;> norm_num
  · rw [Dchi_eps]; norm_num

end CatalanCore.Uniform.Bank.Chi3New
