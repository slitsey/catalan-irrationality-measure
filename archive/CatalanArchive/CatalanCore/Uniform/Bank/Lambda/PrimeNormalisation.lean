import CatalanCore.Uniform.Bank.Lambda.Normalisation
import CatalanCore.Uniform.Content.BankShared.NormaliseGLE
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.BankShared

theorem lambdaScale_units (sgn : Bool) (p : ℕ) [Fact p.Prime] (hp29 : 29 ≤ p) :
    lambdaScale sgn ∈ LocRing p ∧ (lambdaScale sgn)⁻¹ ∈ LocRing p := by
  have hp16 : ¬ p ∣ 16 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 16) hd
    omega
  have h16 : (16 : ℚ) ∈ LocRing p := by
    simpa using int_mem_locRing (ℓ := p) (16 : ℤ)
  have hi16 : (16 : ℚ)⁻¹ ∈ LocRing p := by
    simpa using inv_natCast_mem_locRing (ℓ := p) hp16
  cases sgn
  · exact ⟨h16, hi16⟩
  · refine ⟨(LocRing p).neg_mem h16, ?_⟩
    change (-16 : ℚ)⁻¹ ∈ LocRing p
    simpa only [inv_neg] using (LocRing p).neg_mem hi16

/-- Rank/LP prime bounds on the pipeline transfer to the actual frame unchanged. -/
theorem lambda_family_gle_of_pipeline (sgn : Bool) (depth : ℕ)
    (i : (FL.family (pipeline sgn) depth).ι) (p : ℕ) [Fact p.Prime]
    (hp29 : 29 ≤ p) (e : ℕ) (h : GLE p e ((FL.family (pipeline sgn) depth).Q i)) :
    GLE p e ((FL.family (lambdaFrame sgn) depth).Q i) := by
  obtain ⟨hN, hi⟩ := lambdaScale_units sgn p hp29
  exact normalisation_gle (lambdaFrame sgn) (pipeline sgn) FL.geometry i p e
    (lambdaScale sgn) (lambdaScale_ne_zero sgn) (lambda_Mn_pipeline sgn) hN hi h

#print axioms lambda_family_gle_of_pipeline
end CatalanCore.Uniform.Bank.Lambda
