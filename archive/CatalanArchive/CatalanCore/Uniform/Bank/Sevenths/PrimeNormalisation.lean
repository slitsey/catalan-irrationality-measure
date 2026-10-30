import CatalanCore.Uniform.Bank.Sevenths.Normalisation
import CatalanCore.Uniform.Content.BankShared.NormaliseGLE
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared

theorem sevenths_family_gle_of_pipeline (a : Fin 6) (depth : ℕ)
    (i : (F7.family (pipelineFrame a) depth).ι) (p : ℕ) [Fact p.Prime]
    (hp64 : 64 ≤ p) (e : ℕ) (h : GLE p e ((F7.family (pipelineFrame a) depth).Q i)) :
    GLE p e ((F7.family (seventhsFrameAt a) depth).Q i) := by
  have h49 : ¬ p ∣ 49 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 49) hd
    omega
  have hN : (49 : ℚ) ∈ LocRing p := by
    simpa using int_mem_locRing (ℓ := p) (49 : ℤ)
  have hi : (49 : ℚ)⁻¹ ∈ LocRing p := by
    simpa using inv_natCast_mem_locRing (ℓ := p) h49
  exact normalisation_gle (seventhsFrameAt a) (pipelineFrame a) F7.geometry i p e
    49 (by norm_num) (sevenths_Mn_normalise a) hN hi h

#print axioms sevenths_family_gle_of_pipeline
end CatalanCore.Uniform.Bank.Sevenths
