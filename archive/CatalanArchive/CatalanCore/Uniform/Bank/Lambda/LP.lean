import CatalanCore.Uniform.Bank.Lambda.LPWindows
import CatalanCore.Uniform.Content.Wire.LP
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Uniform.Content.Smith

/-- First strict-LP data for the actual one-fifth geometry. -/
theorem FL_lp1_hyp (a p r : ℕ) [Fact p.Prime] (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1) (hr : r % 2 = 0)
    (hcut : 3 * r ≤ 5 * p) (hrp : p ≤ r)
    (hupper : 4 * r ≤ (4 + root4 a p) * p) :
    LP1Hyp (pipelineFrame a ha) p 4 (4 - a) r (FL.borderSize r)
      (pole4 a p + 1) (root4 a p) := by
  obtain ⟨hj, hk, hk0, hkp, hj0⟩ := one_based_pole4 a p ha hp29 hodd
  have hN := lp1_size_of_cut r (FL.borderSize r) p hr (FL_border_round hr).1 hcut
  have hUk : r < p + (pole4 a p + 1) := by
    rcases ha with rfl | rfl <;> rcases hj with hj | hj <;> rw [hj] at hk hupper <;> omega
  exact pipeline_lp1_hyp a p r (FL.borderSize r) ha hp29 hodd hN hrp hUk

/-- Second strict-LP data for the actual geometry, with exact border rounding. -/
theorem FL_lp2_hyp (a p r : ℕ) [Fact p.Prime] (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1) (hr : r % 2 = 0)
    (hcut : 24 * r ≤ 5 * (4 + root4 a p) * p) (hrp : r < p)
    (hupper : p < r + FL.borderSize r) :
    LP2Hyp (pipelineFrame a ha) p 4 (4 - a) r (FL.borderSize r)
      (pole4 a p + 1) (root4 a p) := by
  obtain ⟨hj, hk, hk0, hkp, hj0⟩ := one_based_pole4 a p ha hp29 hodd
  have hm := (FL_border_round hr).1
  have hN := lp2_size_of_cut a (root4 a p) r (FL.borderSize r) p
    (pole4 a p + 1) ha hj hr hodd hm hk hcut
  have hkr := lp2_pole_le_scale a (root4 a p) r (FL.borderSize r) p
    (pole4 a p + 1) ha hj hp29 hm hk hupper
  exact pipeline_lp2_hyp a p r (FL.borderSize r) ha hp29 hodd hN hrp hkr

/-- The first concrete LP layer is valid on the exact profile window. -/
theorem FL_lp1_valid (a p r : ℕ) (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1) (hr : r % 2 = 0)
    (hcut : 3 * r ≤ 5 * p) (hrp : p ≤ r)
    (hupper : 4 * r ≤ (4 + root4 a p) * p) :
    CatalanCore.Uniform.Content.Wire.lp1Valid FL (pipelineFrame a ha) 4 (4 - a)
      (fun _ q => pole4 a q + 1) (fun _ q => root4 a q) r p := by
  refine ⟨FL_hyb hr, fun [hpf : Fact p.Prime] => ?_⟩
  rw [CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize]
  exact FL_lp1_hyp a p r ha hp29 hodd hr hcut hrp hupper

/-- The second concrete LP layer is valid on its exact profile window. -/
theorem FL_lp2_valid (a p r : ℕ) (ha : a = 1 ∨ a = 3)
    (hp29 : 29 ≤ p) (hodd : p % 2 = 1) (hr : r % 2 = 0)
    (hcut : 24 * r ≤ 5 * (4 + root4 a p) * p) (hrp : r < p)
    (hupper : p < r + FL.borderSize r) :
    CatalanCore.Uniform.Content.Wire.lp2Valid FL (pipelineFrame a ha) 4 (4 - a)
      (fun _ q => pole4 a q + 1) (fun _ q => root4 a q) r p := by
  refine ⟨FL_hyb hr, fun [hpf : Fact p.Prime] => ?_⟩
  rw [CatalanCore.Uniform.Content.BankShared.geometry_k_eq_borderSize]
  exact ⟨FL_lp2_hyp a p r ha hp29 hodd hr hcut hrp hupper, hupper⟩

#print axioms FL_lp1_hyp
#print axioms FL_lp1_valid
#print axioms FL_lp2_valid
#print axioms FL_lp2_hyp
end CatalanCore.Uniform.Bank.Lambda
