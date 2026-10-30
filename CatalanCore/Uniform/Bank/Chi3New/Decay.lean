module

public import CatalanCore.Uniform.Bank.Chi3.Env
public import CatalanCore.Uniform.Bank.Chi3.Cover.Check
public import CatalanCore.Uniform.Decay.AltDecay
public import CatalanCore.Uniform.Bank.Chi3New.Geom
public import CatalanFrames.P6.Contour

@[expose] public section
set_option Elab.async false

/-! Decay of the chi3 block family from the current generated cover and the generic alternating-bank theorem. The public decay statement and constants are unchanged. -/

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

open CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Nodes

namespace GeneratedDecay
open CatalanCore.Uniform.Bank.Chi3.Cover

theorem tab_RP : TabC.RP = altPieces (1 / 2) := by decide +kernel
theorem tab_CP : TabC.CP = altPieces (1 / 2) := by decide +kernel
theorem tab_Mq : TabC.Mq = 1 + (1 / 2 : ℚ) / 2 := by decide +kernel
theorem energy_ok : energyCheck 30 (altPieces (1 / 2)) (altPieces (1 / 2))
    Cover.Dchi.Inu = true := by decide +kernel
theorem dim_eq : Cover.Dchi.dim = 3 := by decide +kernel
theorem eps_pos : 0 < Cover.Dchi.ε := by decide +kernel
theorem Dt_eq : Cover.Dchi.Dt = Chi3.Dchi.Dt := by decide +kernel
theorem ccert_eq : Cover.Dchi.ccert = Chi3.Dchi.ccert := by decide +kernel

end GeneratedDecay

/-- **Window decay of the chi3 block family**, with the unchanged certified constants. -/
theorem chi3_decay (depth : ℕ) :
    HasScaledDecay (G12.family p6Frame depth) G12.scale (Dchi.Dt : ℝ) (Dchi.ccert : ℝ) := by
  have hm0 : ∀ i, (1 / 3 : ℝ) ≤ p6Frame.μ i := by
    intro i
    have hq : (1 / 3 : ℚ) ≤ p6Frame.μ i := by
      rcases p6_mu i with h | h | h <;> rw [h] <;> norm_num
    have h := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at h
    exact h
  have h := altGeom_hasScaledDecay (1 / 2) half_pos (by norm_num)
    (by decide +kernel : Frame.contourCheck p6Frame = true) p6_hAR
    (by decide +kernel) Cover.TabC GeneratedDecay.tab_RP GeneratedDecay.tab_CP
    GeneratedDecay.tab_Mq Cover.Dchi Cover.Pply Cover.check_true
    (by rw [GeneratedDecay.dim_eq]; rfl) 30 GeneratedDecay.energy_ok
    (m0 := 1 / 3) (by norm_num) hm0 GeneratedDecay.eps_pos depth
  rw [GeneratedDecay.Dt_eq, GeneratedDecay.ccert_eq] at h
  exact h

end CatalanCore.Uniform.Bank.Chi3New
