import CatalanCore.Uniform.Bank.Lambda.Final
import CatalanCore.Uniform.Content.BankShared.BudgetedOne
import CatalanCore.Uniform.Content.BankShared.Budgeted
set_option Elab.async false



namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Lambda
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid Filter Finset

/-- The lambda family at even scales. -/
noncomputable abbrev FamE (Fr : Frame) (depth : ℕ) :=
  (FL.family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)

theorem lambda_content_of_pricing_at (Λ : ℝ) (Fr : Frame) (depth : ℕ) (M : ℕ) [NeZero M] (cE : ℕ)
    (price : (FamE Fr depth).ι → ℕ → ℕ) (cut : (FamE Fr depth).ι → ℕ)
    (gle : ∀ i, (FamE Fr depth).Adm i → ∀ (p : ℕ) [Fact p.Prime],
      GLE p (price i p) ((FamE Fr depth).Q i))
    (zero_ge : ∀ i, (FamE Fr depth).Adm i → ∀ p : ℕ, p.Prime → cut i ≤ p → price i p = 0)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Λ + ε)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c → ⌊(tmpl ε c).tend * FL.scale i⌋₊ < p → price i p = 0)
    (tail_lt : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ⌊(tmpl ε c).tend * FL.scale i⌋₊ < cut i)
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * FL.scale i⌋₊ → p.Prime → (p : ZMod M) = c →
        (price i p : ℝ) ≤ (tmpl ε c).α0 * FL.scale i + B.X (FL.scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ P ∈ (tmpl ε c).l, Covers c (fun p => (price i p : ℝ)) (FL.scale i) P)
    (hE : ∀ i, (FamE Fr depth).Adm i → ∀ p ∈ M.primeFactors,
      price i p ≤ Ecrude cE (FL.scale i) p) :
    HasScaledContent (FamE Fr depth) FL.scale Λ :=
  hasScaledContent_budgeted_lim (FamE Fr depth) FL.scale M
    (fun i => NodeFamily.family_degree Fr FL.geometry depth i) price cut gle zero_ge B Λ tmpl
    hmass tail tail_lt pre cov
    (exc_of_Ecrude (FamE Fr depth) FL.scale M price cE hE)

end CatalanCore.Uniform.Bank.Lambda
