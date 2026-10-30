import CatalanCore.Uniform.Bank.Lambda.RankSetup
import CatalanCore.Uniform.Bank.Lambda.PrimeNormalisation
import CatalanCore.Uniform.Bank.Lambda.MemberIdentity
import CatalanCore.Uniform.Bank.Lambda.Layers
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.BankShared

/-- A physical rank member clears the actual sign's geometry polynomial. -/
theorem lambda_rank_member_gle (sgn : Bool) (depth r p : ℕ) [Fact p.Prime]
    (hr : r % 2 = 0) (hp29 : 29 ≤ p) (S : Finset (FL.geometry r).C)
    (M : RankMember (pipeline sgn) (u4 (pipelineNum sgn)) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin (FL.borderSize r) => r + 2 * (j : ℕ))
      (fun j : Fin (FL.borderSize r) => r + 2 * (j : ℕ) + 1)
      (retainedFin (FL_hyb hr) S) p) :
    GLE p M.price ((FL.family (lambdaFrame sgn) depth).Q ⟨r, S⟩) := by
  apply lambda_family_gle_of_pipeline sgn depth ⟨r, S⟩ p hp29 M.price
  rw [lambda_member_commonMinor (pipeline sgn) depth r hr S]
  exact pipeline_rank_member_gle (pipelineNum sgn) p r (FL.borderSize r)
    (pipelineNum_valid sgn) (retainedFin (FL_hyb hr) S) M

/-- Physical member price bounds transfer with the same deletion depth. -/
theorem lambda_rank_price_supplier (sgn : Bool) (depth r p : ℕ) [Fact p.Prime]
    (hr : r % 2 = 0) (hp29 : 29 ≤ p) (S : Finset (FL.geometry r).C) (A B C D : ℚ)
    (h : ∃ M : RankMember (pipeline sgn) (u4 (pipelineNum sgn)) q4
      (fun c : Fin r => (c : ℕ))
      (fun j : Fin (FL.borderSize r) => r + 2 * (j : ℕ))
      (fun j : Fin (FL.borderSize r) => r + 2 * (j : ℕ) + 1)
      (retainedFin (FL_hyb hr) S) p,
      (M.price : ℚ) ≤ A * r + B * p + C + D * ((r - (retainedFin (FL_hyb hr) S).card : ℕ) : ℚ)) :
    ∃ n : ℕ, GLE p n ((FL.family (lambdaFrame sgn) depth).Q ⟨r, S⟩) ∧
      (n : ℚ) ≤ A * r + B * p + C + D * ((r - S.card : ℕ) : ℚ) := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M.price, lambda_rank_member_gle sgn depth r p hr hp29 S M,
    by simpa only [card_retainedFin] using hM⟩

#print axioms lambda_rank_member_gle
#print axioms lambda_rank_price_supplier
end CatalanCore.Uniform.Bank.Lambda